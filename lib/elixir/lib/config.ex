# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Config do
  @moduledoc ~S"""
  A simple keyword-based configuration API.

  ## Example

  This module is most commonly used to define application configuration,
  typically in `config/config.exs`:

      import Config

      config :some_app,
        key1: "value1",
        key2: "value2"

      import_config "#{config_env()}.exs"

  `import Config` will import the functions `config/2`, `config/3`
  `config_env/0`, `config_target/0`, and `import_config/1`
  to help you manage your configuration.

  `config/2` and `config/3` are used to define key-value configuration
  for a given application. Once Mix starts, it will automatically
  evaluate the configuration file and persist the configuration above
  into `:some_app`'s application environment, which can be accessed in
  as follows:

      "value1" = Application.fetch_env!(:some_app, :key1)

  Finally, the line `import_config "#{config_env()}.exs"` will import
  other config files based on the current configuration environment,
  such as `config/dev.exs` and `config/test.exs`.

  `Config` also provides a low-level API for evaluating and reading
  configuration, under the `Config.Reader` module.

  > #### Avoid application environment in libraries {: .info}
  >
  > If you are writing a library to be used by other developers,
  > it is generally recommended to avoid the application environment, as the
  > application environment is effectively a global storage. Also note that
  > the `config/config.exs` of a library is not evaluated when the library is
  > used as a dependency, as configuration is always meant to configure the
  > current project. For more information, see ["Using application configuration for
  > libraries"](design-anti-patterns.md#using-application-configuration-for-libraries).

  ## Migrating from `use Mix.Config`

  The `Config` module in Elixir was introduced in v1.9 as a replacement to
  `use Mix.Config`, which was specific to Mix and has been deprecated.

  You can leverage `Config` instead of `use Mix.Config` in three steps. The first
  step is to replace `use Mix.Config` at the top of your config files by
  `import Config`.

  The second is to make sure your `import_config/1` calls do not have a
  wildcard character. If so, you need to perform the wildcard lookup
  manually. For example, if you did:

      import_config "../apps/*/config/config.exs"

  It has to be replaced by:

      for config <- "../apps/*/config/config.exs" |> Path.expand(__DIR__) |> Path.wildcard() do
        import_config config
      end

  The last step is to replace all `Mix.env()` calls in the config files with `config_env()`.

  Keep in mind you must also avoid using `Mix.env()` inside your project files.
  To check the environment at _runtime_, you may add a configuration key:

      # config.exs
      ...
      config :my_app, env: config_env()

  Then, in other scripts and modules, you may get the environment with
  `Application.fetch_env!/2`:

      # router.exs
      ...
      if Application.fetch_env!(:my_app, :env) == :prod do
        ...
      end

  The only places where you may access functions from the `Mix` module are
  the `mix.exs` file and inside custom Mix tasks, which are always within
  the `Mix.Tasks` namespace.

  ## `config/runtime.exs`

  For runtime configuration, you can use the `config/runtime.exs` file.
  It is executed right before applications start in both Mix and releases
  (assembled with `mix release`).
  """

  @type config_opts :: [
          imports: [Path.t()] | :disabled,
          env: atom(),
          target: atom()
        ]

  @opts_key {__MODULE__, :opts}
  @config_key {__MODULE__, :config}
  @imports_key {__MODULE__, :imports}

  defp get_opts!(), do: Process.get(@opts_key) || raise_improper_use!()
  defp put_opts(value), do: Process.put(@opts_key, value)
  defp delete_opts(), do: Process.delete(@opts_key)

  defp get_config!(), do: Process.get(@config_key) || raise_improper_use!()
  defp put_config(value), do: Process.put(@config_key, value)
  defp delete_config(), do: Process.delete(@config_key)

  defp get_imports!(), do: Process.get(@imports_key) || raise_improper_use!()
  defp put_imports(value), do: Process.put(@imports_key, value)
  defp delete_imports(), do: Process.delete(@imports_key)

  defp raise_improper_use!() do
    raise "could not set configuration via Config. " <>
            "This usually means you are trying to execute a configuration file " <>
            "directly, instead of reading it with Config.Reader"
  end

  @doc """
  Configures the given `root_key`.

  Keyword lists are always deep-merged.

  ## Examples

  The given `opts` are merged into the existing configuration
  for the given `root_key`. Conflicting keys are overridden by the
  ones specified in `opts`, unless they are keywords, which are
  deep merged recursively. For example, the application configuration
  below

      config :logger,
        level: :warn,

      config :logger,
        level: :info,
        truncate: 1024

  will have a final configuration for `:logger` of:

      [level: :info, truncate: 1024]

  """
  @doc since: "1.9.0"
  def config(root_key, opts) when is_atom(root_key) and is_list(opts) do
    if not Keyword.keyword?(opts) do
      raise ArgumentError, "config/2 expected a keyword list, got: #{inspect(opts)}"
    end

    get_config!()
    |> __merge__([{root_key, opts}])
    |> put_config()
  end

  @doc """
  Configures the given `key` for the given `root_key`.

  Keyword lists are always deep merged.

  ## Examples

  The given `opts` are merged into the existing values for `key`
  in the given `root_key`. Conflicting keys are overridden by the
  ones specified in `opts`, unless they are keywords, which are
  deep merged recursively. For example, the application configuration
  below

      config :ecto, Repo,
        log_level: :warn,
        adapter: Ecto.Adapters.Postgres,
        metadata: [read_only: true]

      config :ecto, Repo,
        log_level: :info,
        pool_size: 10,
        metadata: [replica: true]

  will have a final value of the configuration for the `Repo`
  key in the `:ecto` application of:

      Application.get_env(:ecto, Repo)
      #=> [
      #=>   log_level: :info,
      #=>   pool_size: 10,
      #=>   adapter: Ecto.Adapters.Postgres,
      #=>   metadata: [read_only: true, replica: true]
      #=> ]

  """
  @doc since: "1.9.0"
  def config(root_key, key, opts) when is_atom(root_key) and is_atom(key) do
    get_config!()
    |> __merge__([{root_key, [{key, opts}]}])
    |> put_config()
  end

  @doc """
  Reads the configuration for the given root key.

  This function only reads the configuration from a previous
  `config/2` or `config/3` call. If `root_key` points to an
  application, it does not read its actual application environment.
  Its main use case is to make it easier to access and share
  configuration values across files.

  If the `root_key` was not configured, it returns `nil`.

  ## Examples

      # In config/config.exs
      config :my_app, foo: :bar

      # In config/dev.exs
      config :another_app, foo: read_config(:my_app)[:foo] || raise "missing parent configuration"

  """
  @doc since: "1.18.0"
  def read_config(root_key) when is_atom(root_key) do
    get_config!()[root_key]
  end

  @doc """
  Returns the environment this configuration file is executed on.

  In Mix projects this function returns the environment this configuration
  file is executed on. 
  In releases, returns the `MIX_ENV` specified when running `mix release`.

  This is most often used to execute conditional code:

      if config_env() == :prod do
        config :my_app, :debug, false
      end

  """
  @doc since: "1.11.0"
  defmacro config_env() do
    quote do
      Config.__env__!()
    end
  end

  @doc false
  @spec __env__!() :: atom()
  def __env__!() do
    elem(get_opts!(), 0) || raise "no :env key was given to this configuration file"
  end

  @doc """
  Returns the target this configuration file is executed on.

  This is most often used to execute conditional code:

      if config_target() == :host do
        config :my_app, :debug, false
      end

  """
  @doc since: "1.11.0"
  defmacro config_target() do
    quote do
      Config.__target__!()
    end
  end

  @doc false
  @spec __target__!() :: atom()
  def __target__!() do
    elem(get_opts!(), 1) || raise "no :target key was given to this configuration file"
  end

  @doc ~S"""
  Imports configuration from the given file.

  In case the file doesn't exist, an error is raised.

  If file is a relative, it will be expanded relatively to the
  directory the current configuration file is in.

  ## Examples

  This is often used to emulate configuration across environments:

      import_config "#{config_env()}.exs"

  Note, however, some configuration files, such as `config/runtime.exs`
  does not support imports, as they are meant to be copied across
  systems.
  """
  @doc since: "1.9.0"
  defmacro import_config(file) do
    quote do
      Config.__import__!(Path.expand(unquote(file), __DIR__))
      :ok
    end
  end

  @doc false
  @spec __import__!(Path.t()) :: {term, Code.binding()}
  def __import__!(file) when is_binary(file) do
    import_config!(file, File.read!(file), true)
  end

  @doc false
  @spec __eval__!(Path.t(), binary(), config_opts) :: {keyword, [Path.t()] | :disabled}
  def __eval__!(file, content, opts \\ []) when is_binary(file) and is_list(opts) do
    env = Keyword.get(opts, :env)
    target = Keyword.get(opts, :target)
    imports = Keyword.get(opts, :imports, [])

    previous_opts = put_opts({env, target})
    previous_config = put_config([])
    previous_imports = put_imports(imports)

    try do
      {eval_config, _} = import_config!(file, content, false)

      case get_config!() do
        [] when is_list(eval_config) ->
          {validate!(eval_config, file), get_imports!()}

        pdict_config ->
          {pdict_config, get_imports!()}
      end
    after
      if previous_opts, do: put_opts(previous_opts), else: delete_opts()
      if previous_config, do: put_config(previous_config), else: delete_config()
      if previous_imports, do: put_imports(previous_imports), else: delete_imports()
    end
  end

  defp import_config!(file, contents, raise_when_disabled?) do
    current_imports = get_imports!()

    cond do
      current_imports == :disabled ->
        if raise_when_disabled? do
          raise "import_config/1 is not enabled for this configuration file. " <>
                  "Some configuration files do not allow importing other files " <>
                  "as they are often copied to external systems"
        end

      file in current_imports ->
        raise ArgumentError,
              "attempting to load configuration #{Path.relative_to_cwd(file)} recursively"

      true ->
        put_imports([file | current_imports])
        :ok
    end

    Code.eval_string(contents, [], file: file)
  end

  @doc false
  def __merge__(config1, config2) when is_list(config1) and is_list(config2) do
    Keyword.merge(config1, config2, fn _, app1, app2 ->
      Keyword.merge(app1, app2, &deep_merge/3)
    end)
  end

  defp deep_merge(_key, value1, value2) do
    if Keyword.keyword?(value1) and Keyword.keyword?(value2) do
      Keyword.merge(value1, value2, &deep_merge/3)
    else
      value2
    end
  end

  defp validate!(config, file) do
    Enum.all?(config, fn
      {app, value} when is_atom(app) ->
        if Keyword.keyword?(value) do
          true
        else
          raise ArgumentError,
                "expected config for app #{inspect(app)} in #{Path.relative_to_cwd(file)} " <>
                  "to return keyword list, got: #{inspect(value)}"
        end

      _ ->
        false
    end)

    config
  end
end
