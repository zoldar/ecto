import Kernel, except: [apply: 2]

defmodule Ecto.Query.Builder.Join do
  @moduledoc false

  alias Ecto.Query.Builder
  alias Ecto.Query.{JoinExpr, QueryExpr}

  @doc """
  Escapes a join expression (not including the `on` expression).

  It returns a tuple containing the binds, the on expression (if available)
  and the association expression.

  ## Examples

      iex> escape(quote(do: x in "foo"), [], __ENV__)
      {:x, {"foo", nil}, nil, %{}}

      iex> escape(quote(do: "foo"), [], __ENV__)
      {:_, {"foo", nil}, nil, %{}}

      iex> escape(quote(do: x in Sample), [], __ENV__)
      {:x, {nil, {:__aliases__, [alias: false], [:Sample]}}, nil, %{}}

      iex> escape(quote(do: x in {"foo", Sample}), [], __ENV__)
      {:x, {"foo", {:__aliases__, [alias: false], [:Sample]}}, nil, %{}}

      iex> escape(quote(do: x in {"foo", :sample}), [], __ENV__)
      {:x, {"foo", :sample}, nil, %{}}

      iex> escape(quote(do: c in assoc(p, :comments)), [p: 0], __ENV__)
      {:c, nil, {0, :comments}, %{}}

      iex> escape(quote(do: x in fragment("foo")), [], __ENV__)
      {:x, {:{}, [], [:fragment, [], [raw: "foo"]]}, nil, %{}}

  """
  @spec escape(Macro.t, Keyword.t, Macro.Env.t) :: {[atom], Macro.t | nil, Macro.t | nil, %{}}
  def escape({:in, _, [{var, _, context}, expr]}, vars, env)
      when is_atom(var) and is_atom(context) do
    {_, expr, assoc, params} = escape(expr, vars, env)
    {var, expr, assoc, params}
  end

  def escape({:subquery, _, [expr]}, _vars, _env) do
    {:_, quote(do: Ecto.Query.subquery(unquote(expr))), nil, %{}}
  end

  def escape({:subquery, _, [expr, opts]}, _vars, _env) do
    {:_, quote(do: Ecto.Query.subquery(unquote(expr), unquote(opts))), nil, %{}}
  end

  def escape({:fragment, _, [_ | _]} = expr, vars, env) do
    {expr, {params, :acc}} = Builder.escape(expr, :any, {%{}, :acc}, vars, env)
    {:_, expr, nil, params}
  end

  def escape({:unsafe_fragment, _, [_ | _]} = expr, vars, env) do
    {expr, {params, :acc}} = Builder.escape(expr, :any, {%{}, :acc}, vars, env)
    {:_, expr, nil, params}
  end

  def escape({:__aliases__, _, _} = module, _vars, _env) do
    {:_, {nil, module}, nil, %{}}
  end

  def escape(string, _vars, _env) when is_binary(string) do
    {:_, {string, nil}, nil, %{}}
  end

  def escape({string, {:__aliases__, _, _} = module}, _vars, _env) when is_binary(string) do
    {:_, {string, module}, nil, %{}}
  end

  def escape({string, atom}, _vars, _env) when is_binary(string) and is_atom(atom) do
    {:_, {string, atom}, nil, %{}}
  end

  def escape({:assoc, _, [{var, _, context}, field]}, vars, _env)
      when is_atom(var) and is_atom(context) do
    ensure_field!(field)
    var   = Builder.find_var!(var, vars)
    field = Builder.quoted_field!(field)
    {:_, nil, {var, field}, %{}}
  end

  def escape({:^, _, [expr]}, _vars, _env) do
    {:_, quote(do: Ecto.Query.Builder.Join.join!(unquote(expr))), nil, %{}}
  end

  def escape(join, vars, env) do
    case Macro.expand(join, env) do
      ^join ->
        Builder.error! "malformed join `#{Macro.to_string(join)}` in query expression"
      join ->
        escape(join, vars, env)
    end
  end

  @doc """
  Called at runtime to check dynamic joins.
  """
  def join!(expr) when is_atom(expr),
    do: {nil, expr}
  def join!(expr) when is_binary(expr),
    do: {expr, nil}
  def join!({source, module}) when is_binary(source) and is_atom(module),
    do: {source, module}
  def join!(expr),
    do: Ecto.Queryable.to_query(expr)

  @doc """
  Builds a quoted expression.

  The quoted expression should evaluate to a query at runtime.
  If possible, it does all calculations at compile time to avoid
  runtime work.
  """
  @spec build(Macro.t, atom, [Macro.t], Macro.t, Macro.t, Macro.t, atom, Macro.Env.t) ::
              {Macro.t, Keyword.t, non_neg_integer | nil}
  def build(query, qual, binding, expr, count_bind, on, as, env) do
    if not is_atom(as) do
      Builder.error! "`as` must be a compile time atom, got: `#{Macro.to_string(as)}`"
    end

    {query, binding} = Builder.escape_binding(query, binding, env)
    {join_bind, join_source, join_assoc, join_params} = escape(expr, binding, env)
    join_params = Builder.escape_params(join_params)

    qual = validate_qual(qual)
    validate_bind(join_bind, binding)

    {count_bind, query} =
      if join_bind != :_ and !count_bind do
        # If count_bind is not available,
        # we need to compute the amount of binds at runtime
        query =
          quote do
            query = Ecto.Queryable.to_query(unquote(query))
            join_count = Builder.count_binds(query)
            query
          end
        {quote(do: join_count), query}
      else
        {count_bind, query}
      end

    binding = binding ++ [{join_bind, count_bind}]

    next_bind =
      if is_integer(count_bind) do
        count_bind + 1
      else
        quote(do: unquote(count_bind) + 1)
      end

    query = build_on(on || true, as, query, binding, count_bind, qual,
                     join_source, join_assoc, join_params, env)
    {query, binding, next_bind}
  end

  def build_on({:^, _, [var]}, as, query, _binding, count_bind,
               join_qual, join_source, join_assoc, join_params, env) do
    quote do
      query = unquote(query)
      Ecto.Query.Builder.Join.join!(query, unquote(var), unquote(as), unquote(count_bind),
                                    unquote(join_qual), unquote(join_source), unquote(join_assoc),
                                    unquote(join_params), unquote(env.file), unquote(env.line))
    end
  end

  def build_on(on, as, query, binding, count_bind,
               join_qual, join_source, join_assoc, join_params, env) do
    {on_expr, on_params} = Ecto.Query.Builder.Filter.escape(:on, on, count_bind, binding, env)
    on_params = Builder.escape_params(on_params)

    join =
      quote do
        %JoinExpr{qual: unquote(join_qual), source: unquote(join_source),
                  assoc: unquote(join_assoc), as: unquote(as), file: unquote(env.file),
                  line: unquote(env.line), params: unquote(join_params),
                  on: %QueryExpr{expr: unquote(on_expr), params: unquote(on_params),
                                 line: unquote(env.line), file: unquote(env.file)}}
      end

    Builder.apply_query(query, __MODULE__, [join, as, count_bind], env)
  end

  @doc """
  Applies the join expression to the query.
  """
  def apply(%Ecto.Query{joins: joins, aliases: aliases} = query, expr, as, count_bind) do
    new_aliases = apply_aliases(aliases, joins, expr, as, count_bind)

    case new_aliases do
      {:new, aliases} ->
        %{query | joins: joins ++ [expr], aliases: aliases}
      {:unchanged, aliases} ->
        %{query | joins: joins, aliases: aliases}
      new_aliases ->
        aliases = quote do
          {_, aliases} = unquote(new_aliases)
          aliases
        end
        joins = quote do
          case unquote(new_aliases) do
            {:new, _} -> unquote(joins) ++ [unquote(expr)]
            {:unchanged, _} -> unquote(joins)
          end
        end
        %{query | joins: joins, aliases: aliases}
    end
  end
  def apply(query, expr, as, count_bind) do
    apply(Ecto.Queryable.to_query(query), expr, as, count_bind)
  end

  def apply_aliases(aliases, _, _, nil, _), do: {:new, aliases}
  def apply_aliases(aliases, joins, %JoinExpr{} = expr, name, join_count) when is_atom(name) and is_integer(join_count) do
    if Map.has_key?(aliases, name) do
      existing_expr = Enum.at(joins, aliases[name] - 1)

      IO.inspect existing_expr, label: :existing_expr
      IO.inspect expr, label: :new_expr
      if not join_exprs_equal?(existing_expr, expr) do
        Builder.error! "alias `#{inspect name}` already exists"
      else
        {:unchanged, aliases}
      end
    else
      {:new, Map.put(aliases, name, join_count)}
    end
  end
  def apply_aliases(aliases, joins, expr, name, join_count) do
    aliases = case aliases do
      %{} -> Macro.escape(aliases)
      _other -> aliases
    end
    quote do
      Ecto.Query.Builder.Join.apply_aliases(unquote(aliases), unquote(joins), unquote(expr), unquote(name), unquote(join_count))
    end
  end

  defp join_exprs_equal?(%JoinExpr{on: on1} = expr1, %JoinExpr{on: on2} = expr2) do
    sanitize = fn struct ->
      struct
      |> Map.from_struct()
      |> Map.drop([:file, :line])
    end

    [on1, on2, expr1, expr2] = Enum.map([on1, on2, expr1, expr2], &sanitize.(&1))

    %{expr1 | on: on1} == %{expr2 | on: on2}
  end

  @doc """
  Called at runtime to build a join.
  """
  def join!(query, expr, as, count_bind, join_qual, join_source, join_assoc, join_params, file, line) do
    {on_expr, on_params, on_file, on_line} =
      Ecto.Query.Builder.Filter.filter!(:on, query, expr, count_bind, file, line)

    join = %JoinExpr{qual: join_qual, source: join_source, assoc: join_assoc, as: as,
                     file: file, line: line, params: join_params,
                     on: %QueryExpr{expr: on_expr, params: on_params,
                                    line: on_line, file: on_file}}

    apply(query, join, as, count_bind)
  end

  defp validate_qual(qual) when is_atom(qual) do
    qual!(qual)
  end

  defp validate_qual(qual) do
    quote(do: Ecto.Query.Builder.Join.qual!(unquote(qual)))
  end

  defp validate_bind(bind, all) do
    if bind != :_ and bind in all do
      Builder.error! "variable `#{bind}` is already defined in query"
    end
  end

  @qualifiers [:inner, :inner_lateral, :left, :left_lateral, :right, :full, :cross]

  @doc """
  Called at runtime to check dynamic qualifier.
  """
  def qual!(qual) when qual in @qualifiers, do: qual
  def qual!(qual) do
    raise ArgumentError,
      "invalid join qualifier `#{inspect qual}`, accepted qualifiers are: " <>
      Enum.map_join(@qualifiers, ", ", &"`#{inspect &1}`")
  end

  defp ensure_field!({var, _, _}) when var != :^ do
    Builder.error! "you passed the variable `#{var}` to `assoc/2`. Did you mean to pass the atom `:#{var}?`"
  end
  defp ensure_field!(_), do: true
end
