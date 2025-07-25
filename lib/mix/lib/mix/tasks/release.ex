# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Mix.Tasks.Release do
  use Mix.Task

  @shortdoc "Assembles a self-contained release"

  @moduledoc """
  Assembles a self-contained release for the current project:

      $ MIX_ENV=prod mix release
      $ MIX_ENV=prod mix release NAME

  Once a release is assembled, it can be packaged and deployed to a
  target, as long as the target runs on the same operating system (OS)
  distribution and version as the machine running the `mix release`
  command. Windows releases also require Microsoft Visual C++ Runtime.

  A release can be configured in your `mix.exs` file under the `:releases`
  key inside `def project`:

      def project do
        [
          releases: [
            demo: [
              include_executables_for: [:unix],
              applications: [runtime_tools: :permanent]
            ],

            ...
          ]
        ]
      end

  You can specify multiple releases where the key is the release name
  and the value is a keyword list with the release configuration.
  Releasing a certain name is done with:

      $ MIX_ENV=prod mix release demo

  If the given name does not exist, an error is raised.

  If `mix release` is invoked, without specifying a release name, and
  there are multiple releases configured, an error will be raised
  unless you set `default_release: NAME` at the root of your project
  configuration.

  If `mix release` is invoked and there are no releases configured, a
  release is assembled using the application name and default values.

  ## Why releases?

  Releases allow developers to precompile and package all of their code
  and the runtime into a single unit. The benefits of releases are:

    * Code preloading. The VM has two mechanisms for loading code:
      interactive and embedded. By default, it runs in the interactive
      mode which dynamically loads modules when they are used for the
      first time. The first time your application calls `Enum.map/2`,
      the VM will find the `Enum` module and load it. There's a downside:
      when you start a new server in production, it may need to load
      many other modules, causing the first requests to have an unusual
      spike in response time. With releases, the system preloads
      all modules and guarantees your system is ready to handle requests
      after booting.

    * Configuration and customization. Releases give developers fine
      grained control over system configuration and the VM flags used
      to start the system.

    * Self-contained. A release does not require the source code to be
      included in your production artifacts. All of the code is precompiled
      and packaged. Releases do not even require Erlang or Elixir in your
      servers, as it includes the Erlang VM and its runtime by default.
      Furthermore, both Erlang and Elixir standard libraries are stripped
      to bring only the parts you are actually using.

    * Multiple releases. You can assemble different releases with
      different configuration per application or even with different
      applications altogether.

    * Management scripts. Releases come with scripts to start, restart,
      connect to the running system remotely, execute RPC calls, run as
      daemon, run as a Windows service, and more.

  ## Running the release

  Once a release is assembled, you can start it by calling
  `bin/RELEASE_NAME start` inside the release. In production, you would do:

      $ MIX_ENV=prod mix release
      $ _build/prod/rel/my_app/bin/my_app start

  `bin/my_app start` will start the system connected to the current standard
  input/output, where logs are also written to by default. This is the
  preferred way to run the system. Many tools, such as `systemd`, platforms
  as a service, such as Heroku, and many containers platforms, such as Docker,
  are capable of processing the standard input/output and redirecting
  the log contents elsewhere. Those tools and platforms also take care
  of restarting the system in case it crashes.

  You can also execute one-off commands, run the release as a daemon on
  Unix-like system, or install it as a service on Windows. We will take a
  look at those next. You can also list all available commands by invoking
  `bin/RELEASE_NAME`.

  ### One-off commands (eval and rpc)

  If you want to invoke specific modules and functions in your release,
  you can do so in two ways: using `eval` or `rpc`.

      $ bin/RELEASE_NAME eval "IO.puts(:hello)"
      $ bin/RELEASE_NAME rpc "IO.puts(:hello)"

  The `eval` command starts its own instance of the VM but without
  starting any of the applications in the release and without starting
  distribution. For example, if you need to do some prep work before
  running the actual system, like migrating your database, `eval` can
  be a good fit. Just keep in mind any application you may use during
  eval has to be explicitly started.

  You can start an application by calling `Application.ensure_all_started/1`.
  From Elixir v1.16, it is guaranteed the applications have been
  at least loaded. In earlier versions, if you needed to load applications
  but not start them, you also needed to call `Application.load/1`.

  Another way to run commands is with `rpc`, which will connect to the
  system currently running and instruct it to execute the given
  expression. This means you need to guarantee the system was already
  started and be careful with the instructions you are executing.
  You can also use `remote` to connect a remote IEx session to the
  system.

  #### Helper module

  As you operate your system, you may find yourself running some piece of code
  as a one-off command quite often. You may consider creating a module to group
  these tasks:

      # lib/my_app/release_tasks.ex
      defmodule MyApp.ReleaseTasks do
        def eval_purge_stale_data() do
          # Eval commands needs to start the app before
          # Or Application.load(:my_app) if you can't start it
          Application.ensure_all_started(:my_app)

          # Code that purges stale data
          ...
        end

        def rpc_print_connected_users() do
          # Code that print users connected to the current running system
          ...
        end
      end

  In the example above, we prefixed the function names with the command
  name used to execute them, but that is entirely optional.

  And to run them:

      $ bin/RELEASE_NAME eval "MyApp.ReleaseTasks.eval_purge_stale_data()"
      $ bin/RELEASE_NAME rpc "MyApp.ReleaseTasks.rpc_print_connected_users()"

  ### Daemon mode (Unix-like)

  You can run the release in daemon mode with the command:

      $ bin/RELEASE_NAME daemon

  In daemon mode, the system is started on the background via
  [`run_erl`](https://www.erlang.org/doc/apps/erts/run_erl_cmd.html).
  You may also want to enable [`:heart`](`:heart`)
  in daemon mode so it automatically restarts the system in case
  of crashes. See the generated `releases/RELEASE_VSN/env.sh` file.

  The daemon will write all of its standard output to the `tmp/log/`
  directory in the release root. You can watch the log file by doing
  `tail -f tmp/log/erlang.log.1` or similar. Once files get too large,
  the index suffix will be incremented. A developer can also attach
  to the standard input of the daemon by invoking `to_erl tmp/pipe/`
  from the release root. However, note that attaching to the system
  should be done with extreme care, since the usual commands for
  exiting an Elixir system, such as hitting Ctrl+C twice or Ctrl+\\,
  will actually shut down the daemon. Therefore, using
  `bin/RELEASE_NAME remote` should be preferred, even in daemon mode.

  You can customize the tmp directory used both for logging and for
  piping in daemon mode by setting the `RELEASE_TMP` environment
  variable. See the "Customization" section.

  ### Services mode (Windows)

  While daemons are not available on Windows, it is possible to install a
  released system as a service on Windows with the help of
  [`erlsrv`](https://www.erlang.org/doc/apps/erts/erlsrv_cmd.html).
  This can be done by running:

      $ bin/RELEASE_NAME install

  Once installed, the service must be explicitly managed via the `erlsrv`
  executable, which is included in the `erts-VSN/bin` directory.
  The service is not started automatically after installing.

  For example, if you have a release named `demo`, you can install
  the service and then start it from the release root as follows:

      $ bin/demo install
      $ erts-VSN/bin/erlsrv.exe start demo_demo

  The name of the service is `demo_demo` because the name is built
  by concatenating the node name with the release name. Since Elixir
  automatically uses the same name for both, the service will be
  referenced as `demo_demo`.

  The `install` command must be executed as an administrator.

  ### `bin/RELEASE_NAME` commands

  The following commands are supported by `bin/RELEASE_NAME`:

  ```text
  start        Starts the system
  start_iex    Starts the system with IEx attached
  daemon       Starts the system as a daemon (Unix-like only)
  daemon_iex   Starts the system as a daemon with IEx attached (Unix-like only)
  install      Installs this system as a Windows service (Windows only)
  eval "EXPR"  Executes the given expression on a new, non-booted system
  rpc "EXPR"   Executes the given expression remotely on the running system
  remote       Connects to the running system via a remote shell
  restart      Restarts the running system via a remote command
  stop         Stops the running system via a remote command
  pid          Prints the operating system PID of the running system via a remote command
  version      Prints the release name and version to be booted
  ```

  ## Deployments

  ### Requirements

  A release is built on a **host**, a machine which contains Erlang, Elixir,
  and any other dependencies needed to compile your application. A release is
  then deployed to a **target**, potentially the same machine as the host,
  but usually separate, and often there are many targets (either multiple
  instances, or the release is deployed to heterogeneous environments).

  To deploy straight from a host to a separate target, the following must be
  the same between the host and the target:

    * Target architecture (for example, x86_64 or ARM)
    * Target vendor + operating system (for example, Windows, Linux, or Darwin/macOS)
    * Target ABI (for example, musl or gnu)

  This is often represented in the form of target triples, for example,
  `x86_64-unknown-linux-gnu`, `x86_64-unknown-linux-musl`, `x86_64-apple-darwin`.
  If you are building on a MacBook (`x86_64-apple-darwin`) and trying to deploy
  to a typical Ubuntu machine (`x86_64-unknown-linux-gnu`), the release will not
  work. Instead you should build the release on a `x86_64-unknown-linux-gnu` host.

  Typically, different versions of Erlang VM and Elixir are available for
  different targets via package managers, precompiled artifacts, and similar.
  However, to deploy from a host to a separate target, you must also guarantee
  that any dependency with NIFs (Natively-Implemented Functions) are compiled
  for the same triplet. As we will see, this can be done in different ways,
  such as releasing on the target itself, or by using virtual machines or
  containers, usually as part of your release pipeline.

  In addition to matching the target triple, it is also important that the
  target has all of the system packages that your application will need at
  runtime. A common one is the need for OpenSSL when building an application
  that uses `:crypto` or `:ssl`, which is dynamically linked to the Erlang VM.
  Project dependencies containing NIFs (natively-implemented functions) may
  also dynamically link to system libraries, so check those accordingly.

  Of course, some operating systems and package managers can differ between
  versions, so if your goal is to have full compatibility between host and
  target, it is best to ensure the operating system and system package manager
  have the same versions on host and target. This may even be a requirement in
  some systems, especially so with package managers that try to create fully
  reproducible environments (Nix, Guix).

  ### Using matching host and target

  There are a couple of ways to guarantee that a release is built on a host with
  the same properties as the target. A simple option is to fetch the source,
  compile the code and assemble the release on the target itself. It would
  be something like this:

      $ git clone remote://path/to/my_app.git my_app_source
      $ cd my_app_source
      $ mix deps.get --only prod
      $ MIX_ENV=prod mix release
      $ _build/prod/rel/my_app/bin/my_app start

  If you prefer, you can also compile the release to a separate directory,
  so you can erase all source after the release is assembled:

      $ git clone remote://path/to/my_app.git my_app_source
      $ cd my_app_source
      $ mix deps.get --only prod
      $ MIX_ENV=prod mix release --path ../my_app_release
      $ cd ../my_app_release
      $ rm -rf ../my_app_source
      $ bin/my_app start

  However, this option can be expensive if you have multiple production
  nodes or if the release assembling process is a long one, as each node
  needs to individually assemble the release.

  You can automate this process in a couple different ways. One option
  is to make it part of your Continuous Integration (CI) / Continuous
  Deployment (CD) pipeline. When you have a CI/CD pipeline, it is common
  that the machines in your CI/CD pipeline run on the exact same target
  triple as your production servers (if they don't, they should).
  In this case, you can assemble the release at the end of your CI/CD
  pipeline by calling `MIX_ENV=prod mix release` and push the artifact
  to S3 or any other network storage. To perform the deployment, your
  production machines can fetch the deployment from the network storage
  and run `bin/my_app start`.

  ### Using images

  Another mechanism to automate deployments is to use images, such as
  Amazon Machine Images, or container platforms, such as Docker.
  For instance, you can use Docker to run locally a system with the
  exact same target triple as your production servers. Inside the
  container, you can invoke `MIX_ENV=prod mix release` and build
  a complete image and/or container with the operating system, all
  dependencies as well as the releases.

  However, when building such images on your machine, those technologies
  use emulation which may not interplay well with Erlang VM's JIT
  (just-in time) compiler. To address this, you can set this environment
  variable on your build stage:

      ENV ERL_AFLAGS "+JMsingle true"

  ## Shutting down

  Once a system is deployed, shutting down the system can be done by
  sending SIGINT/SIGTERM to the system, which is what most containers,
  platforms and tools do, or by explicitly invoking `bin/RELEASE_NAME stop`.
  Once the system receives the shutdown request, each application and
  their respective supervision trees will stop, one by one, in the
  opposite order that they were started.

  ## Customization

  There are a couple ways in which developers can customize the generated
  artifacts inside a release.

  ### Options

  The following options can be set inside your `mix.exs` on each release definition:

    * `:applications` - a keyword list with application names as keys and their
      mode as value. By default `:applications` includes the current application and
      all applications the current application depends on, recursively. You can include
      new applications or change the mode of existing ones by listing them here.

      The order of the applications given will be preserved as much as possible, with
      only `:kernel`, `:stdlib`, `:sasl`, and `:elixir` listed before the given application
      list. The supported values are:

        * `:permanent` (default) - the application is started and the node shuts down
          if the application terminates, regardless of reason
        * `:transient` - the application is started and the node shuts down
          if the application terminates abnormally
        * `:temporary` - the application is started and the node does not
          shut down if the application terminates
        * `:load` - the application is only loaded
        * `:none` - the application is part of the release but it is neither
          loaded nor started

      If you change the mode of an application, the mode will apply to all its child
      applications. However, if an application has two parents, the mode of the parent
      with highest priority wins (where `:permanent` has the highest priority, according
      to the list above).

    * `:strip_beams` - controls if BEAM files should have their debug information,
      documentation chunks, and other non-essential metadata removed. Defaults to
      `true`. May be set to `false` to disable stripping. Also accepts
      `[keep: ["Docs", "Dbgi"]]` to keep certain chunks that are usually stripped.
      You can also set the `:compress` option to true to enable individual
      compression of BEAM files, although it is typically preferred to compress
      the whole release instead.

    * `:cookie` - a string representing the Erlang Distribution cookie. If this
      option is not set, a random cookie is written to the `releases/COOKIE` file
      when the first release is assembled. At runtime, we will first attempt
      to fetch the cookie from the `RELEASE_COOKIE` environment variable and
      then we'll read the `releases/COOKIE` file.

      If you are setting this option manually, we recommend the cookie option
      to be a long and randomly generated string, such as:
      `Base.encode32(:crypto.strong_rand_bytes(40))`. We also recommend restricting
      the characters in the cookie to only alphanumeric characters and underscore.

    * `:validate_compile_env` - by default a release will match all runtime
      configuration against any configuration that was marked at compile time
      in your application of its dependencies via the `Application.compile_env/3`
      function. If there is a mismatch between those, it means your system is
      misconfigured and unable to boot. You can disable this check by setting
      this option to false.

    * `:path` - the path the release should be installed to.
      Defaults to `"_build/MIX_ENV/rel/RELEASE_NAME"`.

    * `:version` - the release version as a string or `{:from_app, app_name}`.
      Defaults to the current application version. The `{:from_app, app_name}` format
      can be used to easily reference the application version from another application.
      This is particularly useful in umbrella applications.

    * `:quiet` - a boolean that controls if releases should write steps to
      the standard output. Defaults to `false`.

    * `:include_erts` - a boolean, string, or anonymous function of arity zero.
      If a boolean, it indicates whether the Erlang Runtime System (ERTS), which
      includes the Erlang VM, should be included in the release. The default is
      `true`, which is also the recommended value. If a string, it represents
      the path to an existing ERTS installation. If an anonymous function of
      arity zero, it's a function that returns any of the above (boolean or string).

      You may also set this option to `false` if you desire to use the ERTS version installed
      on the target. Note, however, that the ERTS version on the target must have **the
      exact version** as the ERTS version used when the release is assembled. Setting it to
      `false` also disables hot code upgrades. Therefore, `:include_erts` should be
      set to `false` with caution and only if you are assembling the release on the
      same server that runs it.

    * `:include_executables_for` - a list of atoms detailing for which Operating
      Systems executable files should be generated for. By default, it is set to
      `[:unix, :windows]`. You can customize those as follows:

          releases: [
            demo: [
              include_executables_for: [:unix] # Or [:windows] or []
            ]
          ]

    * `:rel_templates_path` - the path to find template files that are copied to
      the release, such as `vm.args.eex`, `remote.vm.args.eex`, `env.sh.eex`
      (or `env.bat.eex`), and `overlays`. Defaults to `"rel"` in the project root.

    * `:overlays` - a list of directories with extra files to be copied
      as is to the release. The "overlays" directory at `:rel_templates_path`
      is always included in this list by default (typically at `"rel/overlays"`).
      See the "Overlays" section for more information.

    * `:steps` - a list of steps to execute when assembling the release. See
      the "Steps" section for more information.

    * `:skip_mode_validation_for` - a list of application names
      (atoms) specifying applications to skip strict validation of
      "unsafe" modes. An "unsafe" case is when a parent application
      mode is `:permanent` but one of the applications it depends on
      is set to `:load`. Use this with care, as a release with
      invalid modes may no longer boot without additional tweaks.
      Defaults to `[]`.

  Note each release definition can be given as an anonymous function. This
  is useful if some release attributes are expensive to compute:

      releases: [
        demo: fn ->
          [version: @version <> "+" <> git_ref()]
        end
      ]

  Besides the options above, it is possible to customize the generated
  release with custom files, by tweaking the release steps or by running
  custom options and commands on boot. We will detail both approaches next.

  ### Overlays

  Often it is necessary to copy extra files to the release root after
  the release is assembled. This can be easily done by placing such
  files in the `rel/overlays` directory. Any file in there is copied
  as is to the release root. For example, if you have placed a
  `rel/overlays/Dockerfile` file, the "Dockerfile" will be copied as
  is to the release root.

  If you want to specify extra overlay directories, you can do so
  with the `:overlays` option. If you need to copy files dynamically,
  see the "Steps" section.

  ### Steps

  It is possible to add one or more steps before and after the release is
  assembled. This can be done with the `:steps` option:

      releases: [
        demo: [
          steps: [&set_configs/1, :assemble, &copy_extra_files/1]
        ]
      ]

  The `:steps` option must be a list and it must always include the
  atom `:assemble`, which does most of the release assembling. You
  can pass anonymous functions before and after the `:assemble` to
  customize your release assembling pipeline. Those anonymous functions
  will receive a `Mix.Release` struct and must return the same or
  an updated `Mix.Release` struct. It is also possible to build a tarball
  of the release by passing the `:tar` step anywhere after `:assemble`.
  If the release `:path` is not configured, the tarball is created in
  `_build/MIX_ENV/RELEASE_NAME-RELEASE_VSN.tar.gz` Otherwise it is
  created inside the configured `:path`.

  See `Mix.Release` for more documentation on the struct and which
  fields can be modified. Note that the `:steps` field itself can be
  modified and it is updated every time a step is called. Therefore,
  if you need to execute a command before and after assembling the
  release, you only need to declare the first steps in your pipeline
  and then inject the last step into the release struct. The steps
  field can also be used to verify if the step was set before or
  after assembling the release.

  ### vm.args and env.sh (env.bat)

  Developers may want to customize the VM flags and environment variables
  given when the release starts. The simplest way to customize those files
  is by running `mix release.init`. The Mix task will copy custom
  `rel/vm.args.eex`, `rel/remote.vm.args.eex`,  `rel/env.sh.eex`, and
  `rel/env.bat.eex` files to your project root. You can modify those files
  and they will be evaluated every time you perform a new release. Those
  files are regular EEx templates and they have a single assign, called
  `@release`, with the `Mix.Release` struct.

  The `vm.args` and `remote.vm.args` files may contain any of the VM flags
  accepted by the [`erl` command](https://www.erlang.org/doc/man/erl.html).

  The `env.sh` and `env.bat` is used to set environment variables.
  In there, you can set vars such as `RELEASE_NODE`, `RELEASE_COOKIE`,
  and `RELEASE_TMP` to customize your node name, cookie and tmp
  directory respectively. Whenever `env.sh` or `env.bat` is invoked,
  the variables `RELEASE_ROOT`, `RELEASE_NAME`, `RELEASE_VSN`, and
  `RELEASE_COMMAND` have already been set, so you can rely on them.
  See the section on environment variables for more information.

  Furthermore, while the `vm.args` files are static, you can use
  `env.sh` and `env.bat` to dynamically set VM options. For example,
  if you want to make sure the Erlang Distribution listens only on
  a given port known at runtime, you can set the following:

  ```bash
  case $RELEASE_COMMAND in
    start*|daemon*)
      ELIXIR_ERL_OPTIONS="-kernel inet_dist_listen_min $BEAM_PORT inet_dist_listen_max $BEAM_PORT"
      export ELIXIR_ERL_OPTIONS
      ;;
    *)
      ;;
  esac
  ```

  Note we only set the port on start/daemon commands. If you also limit
  the port on other commands, such as `rpc`, then you will be unable
  to establish a remote connection as the port will already be in use
  by the node.

  On Windows, your `env.bat` would look like this:

  ```bash
  IF NOT %RELEASE_COMMAND:start=%==%RELEASE_COMMAND% (
    set ELIXIR_ERL_OPTIONS="-kernel inet_dist_listen_min %BEAM_PORT% inet_dist_listen_max %BEAM_PORT%"
  )
  ```

  Inside `env.sh` and `env.bat` files you can access command-line arguments given to release commands.
  For example, given this `env.sh.eex`:

  ```bash
  echo $@
  ```

  or this `env.bat.eex`:

  ```bash
  echo %*
  ```

  starting the release with `bin/myapp start --foo bar baz` will print `start --foo bar baz`.

  ### `epmd`-less deployment

  When a distributed Erlang/Elixir node starts, it runs a separate daemon called EPMD
  (Erlang Port Mapper Daemon) and registers the node name within EPMD. It is possible
  to skip this additional Operating System process by setting the following flags in
  your vm.args files:

      # In vm.args.eex
      -start_epmd false -erl_epmd_port 6789

      # In remote.vm.args.eex
      -start_epmd false -erl_epmd_port 6789 -dist_listen false

  You can pick any port of your choice.

  ## Application configuration

  Mix provides two mechanisms for configuring the application environment
  of your application and your dependencies: build-time and runtime. On this
  section, we will learn how those mechanisms apply to releases. An introduction
  to this topic can be found in the "Configuration" section of the `Mix` module.

  ### Build-time configuration

  Whenever you invoke a `mix` command, Mix loads the configuration in
  `config/config.exs`, if said file exists. We say that this configuration
  is a build-time configuration as it is evaluated whenever you compile your
  code or whenever you assemble the release.

  In other words, if your configuration does something like:

      import Config
      config :my_app, :secret_key, System.fetch_env!("MY_APP_SECRET_KEY")

  The `:secret_key` key under `:my_app` will be computed on the
  host machine, whenever the release is built. Therefore if the machine
  assembling the release not have access to all environment variables used
  to run your code, loading the configuration will fail as the environment
  variable is missing. Luckily, Mix also provides runtime configuration,
  which should be preferred and we will see next.

  ### Runtime configuration

  To enable runtime configuration in your release, create a file named
  `config/runtime.exs`:

      import Config
      config :my_app, :secret_key, System.fetch_env!("MY_APP_SECRET_KEY")

  This file will be executed whenever your Mix project or your release
  starts.

  Your `config/runtime.exs` file needs to follow three important rules:

    * It MUST `import Config` at the top instead of the deprecated `use Mix.Config`
    * It MUST NOT import any other configuration file via `import_config`
    * It MUST NOT access `Mix` in any way, as `Mix` is a build tool and
      it is not available inside releases

  If a `config/runtime.exs` exists, it will be copied to your release
  and executed early in the boot process, when only Elixir and Erlang's
  main applications have been started.

  You can change the path to the runtime configuration file by setting
  `:runtime_config_path` inside each release configuration. This path is
  resolved at build time as the given configuration file is always copied
  to inside the release:

      releases: [
        demo: [
          runtime_config_path: ...
        ]
      ]

  By setting `:runtime_config_path` to `false` it can be used to prevent
  a runtime configuration file to be included in the release.

  ### Config providers

  Releases also supports custom mechanisms, called config providers, to load
  any sort of runtime configuration to the system while it boots. For instance,
  if you need to access a vault or load configuration from a JSON file, it can
  be achieved with config providers. The runtime configuration outlined in the
  previous section is handled by the `Config.Reader` provider. See the
  `Config.Provider` module for more information and more examples.

  The following options can be set inside your releases key in your `mix.exs`
  to control how config providers work:

    * `:reboot_system_after_config` - reboot the system after configuration
      so you can configure system applications, such as `:kernel` and `:stdlib`,
      in your `config/runtime.exs`. Generally speaking, it is best to configure
      `:kernel` and `:stdlib` using the `vm.args` file but this option is available
      for those who need more complex configuration. When set to `true`, the
      release will first boot in interactive mode to compute a config file and
      write it to the "tmp" directory. Then it reboots in the configured `RELEASE_MODE`.
      You can configure the "tmp" directory by setting the `RELEASE_TMP` environment
      variable, either explicitly or inside your `releases/RELEASE_VSN/env.sh`
      (or `env.bat` on Windows). Defaults to `true` if using the deprecated
      `config/releases.exs`, `false` otherwise. Be careful of which libraries you
      load when setting this option to true, if a library is loaded early during
      configuration and it includes native code, it may not actually be able to
      restart cleanly.

    * `:prune_runtime_sys_config_after_boot` - if `:reboot_system_after_config`
      is set, every time your system boots, the release will write a config file
      to your tmp directory. These configuration files are generally small.
      But if you are concerned with disk space or if you have other restrictions,
      you can ask the system to remove said config files after boot. The downside
      is that you will no longer be able to restart the system internally (neither
      via `System.restart/0` nor `bin/RELEASE_NAME restart`). If you need a restart,
      you will have to terminate the Operating System process and start a new
      one. Defaults to `false`.

    * `:start_distribution_during_config` - if `:reboot_system_after_config` is
      set, releases only start the Erlang VM distribution features after the config
      files are evaluated. You can set it to `true` if you need distribution during
      configuration. Defaults to `false`.

    * `:config_providers` - a list of tuples with custom config providers.
      See `Config.Provider` for more information. Defaults to `[]`.

  ### Customization and configuration summary

  Generally speaking, the following files are available for customizing
  and configuring the running system:

    * `config/config.exs` (and `config/prod.exs`) - provides build-time
      application configuration, which are executed when the release is
      assembled

    * `config/runtime.exs` - provides runtime application configuration.
      It is executed every time your Mix project or your release boots
      and is further extensible via config providers. If you want to
      detect you are inside a release, you can check for release specific
      environment variables, such as `RELEASE_NODE` or `RELEASE_MODE`

    * `rel/vm.args.eex` and `rel/remote.vm.args.eex` - template files that
      are copied into every release and provides static configuration of the
      Erlang Virtual Machine and other runtime flags. `vm.args` runs on
      `start`, `daemon`, and `eval` commands. `remote.vm.args` configures
      the VM for `remote` and `rpc` commands

    * `rel/env.sh.eex` and `rel/env.bat.eex` - template files that are copied
      into every release and are executed on every command to set up environment
      variables, including specific ones to the VM, and the general environment

  ## Directory structure

  A release is organized as follows:

  ```text
  bin/
    RELEASE_NAME
  erts-ERTS_VSN/
  lib/
    APP_NAME-APP_VSN/
      ebin/
      include/
      priv/
  releases/
    RELEASE_VSN/
      consolidated/
      elixir
      elixir.bat
      env.bat
      env.sh
      iex
      iex.bat
      remote.vm.args
      runtime.exs
      start.boot
      start.script
      start_clean.boot
      start_clean.script
      sys.config
      vm.args
    COOKIE
    start_erl.data
  tmp/
  ```

  We document this structure for completeness. In practice, developers
  should not modify any of those files after the release is assembled.
  Instead use env scripts, custom config provider, overlays, and all
  other mechanisms described here to configure how your release works.

  ## Environment variables

  The system sets different environment variables. The following variables
  are set early on and can only be read by `env.sh` and `env.bat`:

    * `RELEASE_ROOT` - points to the root of the release. If the system
      includes ERTS, then it is the same as `:code.root_dir/0`. This
      variable is always computed and it cannot be set to a custom value

    * `RELEASE_COMMAND` - the command given to the release, such as `"start"`,
      `"remote"`, `"eval"`, and so on. This is typically accessed inside `env.sh`
      and `env.bat` to set different environment variables under different
      conditions. Note, however, that `RELEASE_COMMAND` has not been
      validated by the time `env.sh` and `env.bat` are called, so it may
      be empty or contain invalid values. This variable is always computed
      and it cannot be set to a custom value

    * `RELEASE_NAME` - the name of the release. It can be set to a custom
      value when invoking the release

    * `RELEASE_VSN` - the version of the release, otherwise the latest
      version is used. It can be set to a custom value when invoking the
      release. The custom value must be an existing release version in
      the `releases/` directory

    * `RELEASE_PROG` - the command line executable used to start the release

  The following variables can be set before you invoke the release or
  inside `env.sh` and `env.bat`:

    * `RELEASE_COOKIE` - the release cookie. By default uses the value
      in `releases/COOKIE`. It can be set to a custom value

    * `RELEASE_NODE` - the release node name, in the format `name` or
      optionally `name@host` if running in distributed mode. It can be
      set to a custom value. The name part must be made only of letters,
      digits, underscores, and hyphens

    * `RELEASE_SYS_CONFIG` - the location of the sys.config file. It can
      be set to a custom path and it must not include the `.config` extension

    * `RELEASE_VM_ARGS` - the location of the vm.args file. It can be set
      to a custom path

    * `RELEASE_REMOTE_VM_ARGS` - the location of the remote.vm.args file.
      It can be set to a custom path

    * `RELEASE_TMP` - the directory in the release to write temporary
      files to. It can be set to a custom directory. It defaults to
      `$RELEASE_ROOT/tmp`

    * `RELEASE_MODE` - if the release should load code on demand (interactive)
      or preload it (embedded). Defaults to "embedded", which increases boot
      time but it means the runtime will respond faster as it doesn't have to
      load code. Choose interactive if you need to decrease boot time and reduce
      memory usage on boot. It applies only to start/daemon/install commands

    * `RELEASE_DISTRIBUTION` - how do we want to run the distribution.
      May be `name` (long names), `sname` (short names) or `none`
      (distribution is not started automatically). Defaults to `sname`.
      When connecting nodes across hosts, you typically want to set
      this to `name` (required to use IPs as host names)

    * `RELEASE_BOOT_SCRIPT` - the name of the boot script to use when starting
      the release. This script is used when running commands such as `start` and
      `daemon`. The boot script is expected to be located at the
      path `releases/RELEASE_VSN/RELEASE_BOOT_SCRIPT.boot`. Defaults to `start`

    * `RELEASE_BOOT_SCRIPT_CLEAN` - the name of the boot script used when
      starting the release clean, without your application or its dependencies.
      This script is used by commands such as `eval`, `rpc`, and `remote`.
      The boot script is expected to be located at the path
      `releases/RELEASE_VSN/RELEASE_BOOT_SCRIPT_CLEAN.boot`. Defaults
      to `start_clean`

  ## Umbrellas

  Releases are well integrated with umbrella projects, allowing you to
  release one or more subsets of your umbrella children. The only difference
  between performing a release in the umbrella project compared to a
  regular application is that umbrellas require you to explicitly list
  your release and the starting point for each release. For example,
  imagine this umbrella applications:

  ```text
  my_app_umbrella/
    apps/
      my_app_core/
      my_app_event_processing/
      my_app_web/
  ```

  where both `my_app_event_processing` and `my_app_web` depend on
  `my_app_core` but they do not depend on each other.

  Inside your umbrella, you can define multiple releases:

      releases: [
        web_and_event_processing: [
          applications: [
            my_app_event_processing: :permanent,
            my_app_web: :permanent
          ]
        ],

        web_only: [
          applications: [my_app_web: :permanent]
        ],

        event_processing_only: [
          applications: [my_app_event_processing: :permanent]
        ]
      ]

  Note you don't need to define all applications in `:applications`,
  only the entry points. Also remember that the recommended mode
  for all applications in the system is `:permanent`.

  Finally, keep in mind it is not required for you to assemble the
  release from the umbrella root. You can also assemble the release
  from each child application individually. Doing it from the root,
  however, allows you to include two applications that do not depend
  on each other as part of the same release.

  ## Hot Code Upgrades

  Erlang and Elixir are sometimes known for the capability of upgrading
  a node that is running in production without shutting down that node.
  However, this feature is not supported out of the box by Elixir releases.

  The reason we don't provide hot code upgrades is because they are very
  complicated to perform in practice, as they require careful coding of
  your processes and applications as well as extensive testing. Given most
  teams can use other techniques that are language agnostic to upgrade
  their systems, such as Blue/Green deployments, Canary deployments,
  Rolling deployments, and others, hot upgrades are rarely a viable
  option. Let's understand why.

  In a hot code upgrade, you want to update a node from version A to
  version B. To do so, the first step is to write recipes for every application
  that changed between those two releases, telling exactly how the application
  changed between versions, those recipes are called `.appup` files.
  While some of the steps in building `.appup` files can be automated,
  not all of them can. Furthermore, each process in the application needs
  to be explicitly coded with hot code upgrades in mind. Let's see an example.
  Imagine your application has a counter process as a GenServer:

      defmodule Counter do
        use GenServer

        def start_link(_) do
          GenServer.start_link(__MODULE__, :ok, name: __MODULE__)
        end

        def bump do
          GenServer.call(__MODULE__, :bump)
        end

        ## Callbacks

        def init(:ok) do
          {:ok, 0}
        end

        def handle_call(:bump, counter) do
          {:reply, :ok, counter + 1}
        end
      end

  You add this process as part of your supervision tree and ship version
  0.1.0 of your system. Now let's imagine that on version 0.2.0 you added
  two changes: instead of `bump/0`, that always increments the counter by
  one, you introduce `bump/1` that passes the exact value to bump the
  counter. You also change the state, because you want to store the maximum
  bump value:

      defmodule Counter do
        use GenServer

        def start_link(_) do
          GenServer.start_link(__MODULE__, :ok, name: __MODULE__)
        end

        def bump(by) do
          GenServer.call(__MODULE__, {:bump, by})
        end

        ## Callbacks

        def init(:ok) do
          {:ok, {0, 0}}
        end

        def handle_call({:bump, by}, {counter, max}) do
          {:reply, :ok, {counter + by, max(max, by)}}
        end
      end

  If you were to perform a hot code upgrade in such an application, it would
  crash, because in the initial version the state was just a counter
  but in the new version the state is a tuple. Furthermore, you changed
  the format of the `call` message from `:bump` to `{:bump, by}` and
  the process may have both old and new messages temporarily mixed, so
  we need to handle both. The final version would be:

      defmodule Counter do
        use GenServer

        def start_link(_) do
          GenServer.start_link(__MODULE__, :ok, name: __MODULE__)
        end

        def bump(by) do
          GenServer.call(__MODULE__, {:bump, by})
        end

        ## Callbacks

        def init(:ok) do
          {:ok, {0, 0}}
        end

        def handle_call(:bump, {counter, max}) do
          {:reply, :ok, {counter + 1, max(max, 1)}}
        end

        def handle_call({:bump, by}, {counter, max}) do
          {:reply, :ok, {counter + by, max(max, by)}}
        end

        def code_change(_, counter, _) do
          {:ok, {counter, 0}}
        end
      end

  Now you can proceed to list this process in the `.appup` file and
  hot code upgrade it. This is one of the many steps necessary
  to perform hot code upgrades and it must be taken into account by
  every process and application being upgraded in the system.
  The [`.appup` cookbook](https://www.erlang.org/doc/design_principles/appup_cookbook.html)
  provides a good reference and more examples.

  Once `.appup`s are created, the next step is to create a `.relup`
  file with all instructions necessary to update the release itself.
  Erlang documentation does provide a chapter on
  [Creating and upgrading a target system](https://www.erlang.org/doc/system_principles/create_target.html).
  [Learn You Some Erlang has a chapter on hot code upgrades](https://learnyousomeerlang.com/relups).

  Overall, there are many steps, complexities and assumptions made
  during hot code upgrades, which is ultimately why they are not
  provided by Elixir out of the box. However, hot code upgrades can
  still be achieved by teams who desire to implement those steps
  on top of `mix release` in their projects or as separate libraries.

  ## Command line options

    * `--force` - forces recompilation
    * `--no-archives-check` - does not check archive
    * `--no-deps-check` - does not check dependencies
    * `--no-elixir-version-check` - does not check Elixir version
    * `--no-compile` - does not compile before assembling the release
    * `--overwrite` - overwrite existing files instead of prompting the user for action
    * `--path` - the path of the release
    * `--quiet` - does not write progress to the standard output
    * `--version` - the version of the release

  """

  import Mix.Generator

  @switches [
    overwrite: :boolean,
    force: :boolean,
    quiet: :boolean,
    path: :string,
    version: :string,
    compile: :boolean,
    deps_check: :boolean,
    archives_check: :boolean,
    elixir_version_check: :boolean
  ]

  @aliases [
    f: :force
  ]

  @impl true
  def run(args) do
    Mix.Project.get!()
    Mix.Task.run("compile", args)
    Mix.ensure_application!(:sasl)
    Mix.ensure_application!(:crypto)

    config = Mix.Project.config()

    release =
      case OptionParser.parse!(args, strict: @switches, aliases: @aliases) do
        {overrides, [name]} -> Mix.Release.from_config!(String.to_atom(name), config, overrides)
        {overrides, []} -> Mix.Release.from_config!(nil, config, overrides)
        {_, _} -> Mix.raise("Expected \"mix release\" or \"mix release NAME\"")
      end

    if not File.exists?(release.version_path) or
         yes?(release, "Release #{release.name}-#{release.version} already exists. Overwrite?") do
      run_steps(release)
    end
  end

  defp yes?(release, message) do
    release.options[:overwrite] or Mix.shell().yes?(message)
  end

  defp run_steps(%{steps: [step | steps]} = release) when is_function(step) do
    case step.(%{release | steps: steps}) do
      %Mix.Release{} = release ->
        run_steps(release)

      other ->
        Mix.raise(
          "Expected step #{inspect(step)} to return a Mix.Release, got: #{inspect(other)}"
        )
    end
  end

  defp run_steps(%{steps: [:tar | steps]} = release) do
    %{release | steps: steps} |> make_tar() |> run_steps()
  end

  defp run_steps(%{steps: [:assemble | steps]} = release) do
    %{release | steps: steps} |> assemble() |> run_steps()
  end

  defp run_steps(%{steps: []} = release) do
    announce(release)
  end

  defp assemble(release) do
    config = Mix.Project.config()
    message = "#{release.name}-#{release.version} on MIX_ENV=#{Mix.env()}"
    info(release, [:green, "* assembling ", :reset, message])

    # releases/
    #   VERSION/
    #     consolidated/
    #     NAME.rel
    #     start.boot
    #     start.script
    #     start_clean.boot
    #     start_clean.script
    #     sys.config
    # releases/
    #   COOKIE
    #   start_erl.data
    {consolidation_path, release} = build_rel(release, config)

    [
      # erts-VSN/
      :erts,
      # releases/VERSION/consolidated
      {:consolidated, consolidation_path},
      # bin/
      #   RELEASE_NAME
      #   RELEASE_NAME.bat
      #   start
      #   start.bat
      # releases/
      #   VERSION/
      #     elixir
      #     elixir.bat
      #     iex
      #     iex.bat
      {:executables, Keyword.get(release.options, :include_executables_for, [:unix, :windows])}
      # lib/APP_NAME-APP_VSN/
      | Map.keys(release.applications)
    ]
    |> Task.async_stream(&copy(&1, release), ordered: false, timeout: :infinity)
    |> Stream.run()

    copy_overlays(release)
  end

  defp make_tar(release) do
    build_path = Mix.Project.build_path()

    dir_path =
      if release.path == Path.join([build_path, "rel", Atom.to_string(release.name)]) do
        build_path
      else
        release.path
      end

    out_path = Path.join(dir_path, "#{release.name}-#{release.version}.tar.gz")
    info(release, [:green, "* building ", :reset, out_path])

    lib_dirs =
      Enum.reduce(release.applications, [], fn {name, app_config}, acc ->
        vsn = Keyword.fetch!(app_config, :vsn)
        [Path.join("lib", "#{name}-#{vsn}") | acc]
      end)

    erts_dir =
      case release.erts_source do
        nil -> []
        _ -> ["erts-#{release.erts_version}"]
      end

    release_files =
      for basename <- File.ls!(Path.join(release.path, "releases")),
          not File.dir?(Path.join([release.path, "releases", basename])),
          do: Path.join("releases", basename)

    dirs =
      ["bin", Path.join("releases", release.version)] ++
        erts_dir ++ lib_dirs ++ release_files

    files =
      dirs
      |> Enum.filter(&File.exists?(Path.join(release.path, &1)))
      |> Kernel.++(release.overlays)
      |> Enum.map(&{String.to_charlist(&1), String.to_charlist(Path.join(release.path, &1))})

    File.rm(out_path)
    :ok = :erl_tar.create(String.to_charlist(out_path), files, [:dereference, :compressed])
    release
  end

  # build_rel

  defp build_rel(release, config) do
    version_path = release.version_path
    File.rm_rf!(version_path)
    File.mkdir_p!(version_path)
    release = maybe_add_config_reader_provider(config, release, version_path)

    consolidation_path =
      if config[:consolidate_protocols] do
        Mix.Project.consolidation_path(config)
      end

    sys_config =
      if File.regular?(config[:config_path]) do
        config[:config_path] |> Config.Reader.read!(env: Mix.env(), target: Mix.target())
      else
        []
      end

    vm_args_path = Path.join(version_path, "vm.args")
    remote_vm_args_path = Path.join(version_path, "remote.vm.args")
    cookie_path = Path.join(release.path, "releases/COOKIE")
    start_erl_path = Path.join(release.path, "releases/start_erl.data")
    config_provider_path = {:system, "RELEASE_SYS_CONFIG", ".config"}

    with :ok <- make_boot_scripts(release, version_path, consolidation_path),
         :ok <- make_vm_args(release, vm_args_path),
         :ok <- make_vm_args(release, remote_vm_args_path),
         :ok <- Mix.Release.make_sys_config(release, sys_config, config_provider_path),
         :ok <- Mix.Release.make_cookie(release, cookie_path),
         :ok <- Mix.Release.make_start_erl(release, start_erl_path) do
      {consolidation_path, release}
    else
      {:error, message} ->
        File.rm_rf!(version_path)
        Mix.raise(message)
    end
  end

  defp maybe_add_config_reader_provider(config, %{options: opts} = release, version_path) do
    default_path = config[:config_path] |> Path.dirname() |> Path.join("runtime.exs")
    deprecated_path = config[:config_path] |> Path.dirname() |> Path.join("releases.exs")

    {path, reboot?} =
      cond do
        opts[:runtime_config_path] == false ->
          {false, false}

        path = opts[:runtime_config_path] ->
          {path, false}

        File.exists?(default_path) ->
          if File.exists?(deprecated_path) do
            IO.warn(
              "both #{inspect(default_path)} and #{inspect(deprecated_path)} have been " <>
                "found, but only #{inspect(default_path)} will be used"
            )
          end

          {default_path, false}

        File.exists?(deprecated_path) ->
          IO.warn(
            "config/releases.exs is deprecated, use config/runtime.exs or set :runtime_config_path in your release configuration instead"
          )

          {deprecated_path, true}

        true ->
          {nil, false}
      end

    cond do
      path ->
        msg = "#{path} to configure the release at runtime"
        info(release, [:green, "* using ", :reset, msg])
        File.cp!(path, Path.join(version_path, "runtime.exs"))
        init = {:system, "RELEASE_ROOT", "/releases/#{release.version}/runtime.exs"}
        opts = [path: init, env: Mix.env(), target: Mix.target(), imports: :disabled]
        release = update_in(release.config_providers, &[{Config.Reader, opts} | &1])
        update_in(release.options, &Keyword.put_new(&1, :reboot_system_after_config, reboot?))

      release.config_providers == [] and path != false ->
        skipping("runtime configuration (#{default_path} not found)")
        release

      true ->
        release
    end
  end

  defp make_boot_scripts(release, version_path, consolidation_path) do
    prepend_paths =
      if consolidation_path do
        ["$RELEASE_LIB/../releases/#{release.version}/consolidated"]
      else
        []
      end

    results =
      for {boot_name, modes} <- release.boot_scripts do
        sys_path = Path.join(version_path, Atom.to_string(boot_name))

        with :ok <- Mix.Release.make_boot_script(release, sys_path, modes, prepend_paths) do
          if boot_name == :start do
            rel_path = Path.join(Path.dirname(sys_path), "#{release.name}.rel")
            File.rename!(sys_path <> ".rel", rel_path)
          else
            File.rm(sys_path <> ".rel")
          end

          :ok
        end
      end

    Enum.find(results, :ok, &(&1 != :ok))
  end

  defp make_vm_args(release, path) do
    vm_args_template = Mix.Release.rel_templates_path(release, "#{Path.basename(path)}.eex")

    if File.exists?(vm_args_template) do
      copy_template(vm_args_template, path, [release: release], force: true)
    else
      File.write!(path, vm_args_template(release: release))
    end

    :ok
  end

  defp announce(release) do
    path = Path.relative_to_cwd(release.path)
    cmd = "#{path}/bin/#{release.name}"

    info(release, """

    Release created at #{path}

        # To start your system
        #{cmd} start

    Once the release is running:

        # To connect to it remotely
        #{cmd} remote

        # To stop it gracefully (you may also send SIGINT/SIGTERM)
        #{cmd} stop

    To list all commands:

        #{cmd}
    """)
  end

  defp info(release, message) do
    if !release.options[:quiet] do
      Mix.shell().info(message)
    end
  end

  defp skipping(message) do
    Mix.shell().info([:yellow, "* skipping ", :reset, message])
  end

  ## Overlays

  defp copy_overlays(release) do
    target = release.path
    default = Mix.Release.rel_templates_path(release, "overlays")

    overlays =
      if File.dir?(default) do
        [default | List.wrap(release.options[:overlays])]
      else
        List.wrap(release.options[:overlays])
      end

    relative =
      overlays
      |> Enum.flat_map(&File.cp_r!(&1, target))
      |> Enum.uniq()
      |> List.delete(target)
      |> Enum.map(&Path.relative_to(&1, target))

    update_in(release.overlays, &(relative ++ &1))
  end

  ## Copy operations

  defp copy(:erts, release) do
    _ = Mix.Release.copy_erts(release)
    :ok
  end

  defp copy(app, release) when is_atom(app) do
    Mix.Release.copy_app(release, app)
  end

  defp copy({:consolidated, consolidation_path}, release) do
    if consolidation_path do
      consolidation_target = Path.join(release.version_path, "consolidated")
      _ = Mix.Release.copy_ebin(release, consolidation_path, consolidation_target)
    end

    :ok
  end

  defp copy({:executables, include_executables_for}, release) do
    elixir_bin_path = Application.app_dir(:elixir, "../../bin")
    bin_path = Path.join(release.path, "bin")
    File.mkdir_p!(bin_path)

    for os <- include_executables_for do
      {env, env_fun, clis} = cli_for(os, release)
      env_path = Path.join(release.version_path, env)
      env_template_path = Mix.Release.rel_templates_path(release, env <> ".eex")

      if File.exists?(env_template_path) do
        copy_template(env_template_path, env_path, [release: release], force: true)
      else
        File.write!(env_path, env_fun.(release))
      end

      for {filename, contents} <- clis do
        target = Path.join(bin_path, filename)
        File.write!(target, contents)
        executable!(target)
      end

      for {filename, contents_fun} <- elixir_cli_for(os, release) do
        source = Path.join(elixir_bin_path, filename)

        if File.regular?(source) do
          target = Path.join(release.version_path, filename)
          File.write!(target, contents_fun.(source))
          executable!(target)
        else
          skipping("#{filename} for #{os} (bin/#{filename} not found in the Elixir installation)")
        end
      end
    end
  end

  defp cli_for(:unix, release) do
    {"env.sh", &env_template(release: &1), [{"#{release.name}", cli_template(release: release)}]}
  end

  defp cli_for(:windows, release) do
    {"env.bat", &env_bat_template(release: &1),
     [{"#{release.name}.bat", cli_bat_template(release: release)}]}
  end

  defp elixir_cli_for(:unix, release) do
    [
      {"elixir",
       &(&1
         |> File.read!()
         |> String.replace(
           ~s[ -elixir_root "$SCRIPT_PATH"/../lib -pa "$SCRIPT_PATH"/../lib/elixir/ebin ],
           " "
         )
         |> replace_erts_bin(release, ~s["$SCRIPT_PATH"/../../erts-#{release.erts_version}/bin/]))},
      {"iex", &File.read!/1}
    ]
  end

  defp elixir_cli_for(:windows, release) do
    [
      {"elixir.bat",
       &(&1
         |> File.read!()
         |> String.replace(
           ~s[ -elixir_root !SCRIPT_PATH!..\\lib -pa !SCRIPT_PATH!..\\lib\\elixir\\ebin ],
           " "
         )
         |> replace_erts_bin(release, ~s[%~dp0\\..\\..\\erts-#{release.erts_version}\\bin\\]))},
      {"iex.bat", &File.read!/1}
    ]
  end

  @erts_bin [~s[ERTS_BIN="$ERTS_BIN"], ~s[ERTS_BIN=!ERTS_BIN!]]

  defp replace_erts_bin(contents, release, new_path) do
    if release.erts_source do
      String.replace(contents, @erts_bin, ~s[ERTS_BIN=#{new_path}])
    else
      contents
    end
  end

  defp executable!(path), do: File.chmod!(path, 0o755)

  # Helper functions

  defp release_mode(release, env_var) do
    reboot? = Keyword.get(release.options, :reboot_system_after_config, false)

    if reboot? and release.config_providers != [] do
      "-elixir config_provider_reboot_mode #{env_var}"
    else
      "-mode #{env_var}"
    end
  end

  embed_template(:vm_args, Mix.Tasks.Release.Init.vm_args_text(false))
  embed_template(:env, Mix.Tasks.Release.Init.env_text())
  embed_template(:cli, Mix.Tasks.Release.Init.cli_text())
  embed_template(:env_bat, Mix.Tasks.Release.Init.env_bat_text())
  embed_template(:cli_bat, Mix.Tasks.Release.Init.cli_bat_text())
end
