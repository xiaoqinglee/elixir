# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

Code.require_file("../../test_helper.exs", __DIR__)

defmodule Mix.Tasks.DepsTest do
  use MixTest.Case

  defmodule DepsApp do
    def project do
      [
        app: :deps,
        version: "0.1.0",
        deps: [
          {:ok, "0.1.0", github: "elixir-lang/ok"},
          {:invalidvsn, "0.2.0", path: "deps/invalidvsn"},
          {:invalidapp, "0.1.0", path: "deps/invalidapp"},
          {:noappfile, "0.1.0", path: "deps/noappfile"},
          {:nosemver, "~> 0.1", path: "deps/nosemver"}
        ]
      ]
    end
  end

  defmodule SuccessfulDepsApp do
    def project do
      [
        app: :sample,
        version: "0.1.0",
        deps: [
          {:ok, "0.1.0", path: "deps/ok"}
        ]
      ]
    end
  end

  defmodule ReqDepsApp do
    def project do
      [
        app: :req_deps,
        version: "0.1.0",
        deps: [
          {:ok, ">= 2.0.0", path: "deps/ok"},
          {:noappfile, path: "deps/noappfile", app: false},
          {:apppath, path: "deps/noappfile", app: "../deps/ok/ebin/ok.app"}
        ]
      ]
    end
  end

  defmodule MissingLocalDepsApp do
    def project do
      [
        app: :missing_local_deps,
        version: "0.1.0",
        deps: [
          {:ok, path: "missing/dep"}
        ]
      ]
    end
  end

  defmodule RawRepoDepApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:raw_repo, "0.1.0", path: "custom/raw_repo"}
        ]
      ]
    end
  end

  ## deps

  test "prints list of dependencies and their status" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DepsApp)

      Mix.Tasks.Deps.run([])

      assert_received {:mix_shell, :info, ["* ok (https://github.com/elixir-lang/ok.git) (mix)"]}
      msg = "  the dependency is not available, run \"mix deps.get\""
      assert_received {:mix_shell, :info, [^msg]}

      assert_received {:mix_shell, :info, ["* invalidvsn (deps/invalidvsn)"]}
      assert_received {:mix_shell, :info, ["  the app file contains an invalid version: :ok"]}

      assert_received {:mix_shell, :info, ["* invalidapp (deps/invalidapp) (mix)"]}
      msg = "  the app file at \"_build/dev/lib/invalidapp/ebin/invalidapp.app\" is invalid"
      assert_received {:mix_shell, :info, [^msg]}

      assert_received {:mix_shell, :info, ["* noappfile (deps/noappfile)"]}
      assert_received {:mix_shell, :info, ["  could not find an app file at" <> _]}

      assert_received {:mix_shell, :info, ["* nosemver (deps/nosemver)"]}
      assert_received {:mix_shell, :info, ["  the app file specified a non-Semantic" <> _]}
    end)
  end

  test "prints list of dependencies and their status, including req mismatches and custom apps" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ReqDepsApp)

      Mix.Tasks.Deps.run([])

      assert_received {:mix_shell, :info, ["* ok (deps/ok) (mix)"]}
      msg = "  the dependency does not match the requirement \">= 2.0.0\", got \"0.1.0\""
      assert_received {:mix_shell, :info, [^msg]}

      assert_received {:mix_shell, :info, ["* apppath (deps/noappfile)"]}
      refute_received {:mix_shell, :info, ["  could not find app file at " <> _]}

      assert_received {:mix_shell, :info, ["* noappfile (deps/noappfile)"]}
      refute_received {:mix_shell, :info, ["  could not find app file at " <> _]}
    end)
  end

  test "prints misspelled dependency name hint" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DepsApp)

      other_app_path = Path.join(Mix.Project.build_path(), "lib/noappfile/ebin/other_app.app")
      File.mkdir_p!(Path.dirname(other_app_path))
      File.write!(other_app_path, "")

      Mix.Tasks.Deps.run([])

      message =
        "  could not find an app file at \"_build/dev/lib/noappfile/ebin/noappfile.app\". " <>
          "Another app file was found in the same directory " <>
          "\"_build/dev/lib/noappfile/ebin/other_app.app\", " <>
          "try changing the dependency name to :other_app"

      assert_received {:mix_shell, :info, ["* noappfile (deps/noappfile)"]}
      assert_received {:mix_shell, :info, [^message]}
    end)
  end

  test "prints Elixir req mismatches" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ReqDepsApp)

      File.write!("deps/ok/mix.exs", """
      defmodule Deps.OkApp do
        use Mix.Project

        def project do
          [elixir: "~> 0.1.0", app: :ok, version: "2.0.0"]
        end
      end
      """)

      Mix.Tasks.Deps.Compile.run([:ok])

      msg =
        "warning: the dependency :ok requires Elixir \"~> 0.1.0\" " <>
          "but you are running on v#{System.version()}"

      assert_received {:mix_shell, :error, [^msg]}

      Mix.Tasks.Deps.Compile.run([])
    end)
  end

  test "prints list of dependencies and their lock status" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DepsApp)

      File.cd!("deps/ok", fn ->
        System.cmd("git", ~w[-c core.hooksPath='' init])
      end)

      Mix.Tasks.Deps.run([])
      assert_received {:mix_shell, :info, ["* ok (https://github.com/elixir-lang/ok.git) (mix)"]}

      msg =
        "  the dependency is not locked. To generate the \"mix.lock\" file run \"mix deps.get\""

      assert_received {:mix_shell, :info, [^msg]}

      Mix.Dep.Lock.write(%{ok: {:git, "https://github.com/elixir-lang/ok.git", "abcdefghi", []}})
      Mix.Tasks.Deps.run([])

      assert_received {:mix_shell, :info, ["* ok (https://github.com/elixir-lang/ok.git) (mix)"]}
      assert_received {:mix_shell, :info, ["  locked at abcdefg"]}

      msg =
        "  lock mismatch: the dependency is out of date. To fetch locked version run \"mix deps.get\""

      assert_received {:mix_shell, :info, [^msg]}

      Mix.Dep.Lock.write(%{
        ok: {:git, "git://github.com/elixir-lang/another.git", "abcdefghi", []}
      })

      Mix.Tasks.Deps.run([])

      assert_received {:mix_shell, :info, ["* ok (https://github.com/elixir-lang/ok.git) (mix)"]}

      msg =
        "  lock outdated: the lock is outdated compared to the options in your mix.exs. To fetch locked version run \"mix deps.get\""

      assert_received {:mix_shell, :info, [^msg]}
    end)
  end

  test "cleans and recompiles artifacts if --force is given" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      Mix.Tasks.Deps.Compile.run([])
      File.touch!("_build/dev/lib/ok/clean-me")

      Mix.Tasks.Deps.Compile.run(["--force"])
      refute File.exists?("_build/dev/lib/ok/clean-me")
    end)
  end

  test "compiles deps using os partitions" do
    System.put_env("MIX_OS_DEPS_COMPILE_PARTITION_COUNT", "2")

    in_fixture("deps_status", fn ->
      File.write!("mix.exs", """
      defmodule ParDepsApp do
        use Mix.Project

        def project do
          [
            app: :par_sample,
            version: "0.1.0",
            deps: [
              {:raw_repo, "0.1.0", path: "custom/raw_repo"},
              {:git_repo, "0.1.0", path: #{inspect(fixture_path("git_repo"))}}
            ]
          ]
        end
      end
      """)

      Mix.Project.in_project(:par_sample, ".", fn _ ->
        output = ExUnit.CaptureIO.capture_io(fn -> Mix.Tasks.Deps.Compile.run([]) end)
        assert output =~ ~r/\d> Generated git_repo app/
        assert output =~ ~r/\d> Generated raw_repo app/
        assert_received {:mix_shell, :info, ["mix deps.compile running across 2 OS processes"]}
      end)
    end)
  after
    System.delete_env("MIX_OS_DEPS_COMPILE_PARTITION_COUNT")
  end

  test "doesn't compile any umbrella apps if --skip-umbrella-children is given" do
    in_fixture("umbrella_dep/deps/umbrella", fn ->
      Mix.Project.in_project(:umbrella, ".", fn _ ->
        Mix.Tasks.Deps.Compile.run(["--skip-umbrella-children"])
        refute File.exists?("_build/dev/lib/foo/ebin")
        refute File.exists?("_build/dev/lib/bar/ebin")
      end)
    end)
  end

  test "doesn't compile any path deps if --skip-local-deps is given" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      File.rm_rf!("_build/dev/lib/ok/ebin")
      Mix.Tasks.Deps.Compile.run(["--skip-local-deps"])
      refute File.exists?("_build/dev/lib/ok/ebin")
    end)
  end

  test "checks if local dependencies are available before compiling" do
    Mix.Project.push(MissingLocalDepsApp)

    error_message =
      "Cannot compile dependency :ok because it isn't available, please ensure the dependency " <>
        "is at \"missing/dep\""

    assert_raise Mix.Error, error_message, fn ->
      Mix.Tasks.Deps.Compile.run([])
    end
  end

  ## deps.loadpaths

  test "checks list of dependencies and their status with success" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      Mix.Tasks.Deps.Loadpaths.run([])
    end)
  end

  test "checks list of dependencies and their status on failure" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DepsApp)

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      assert_received {:mix_shell, :error, ["* ok (https://github.com/elixir-lang/ok.git)"]}
      msg = "  the dependency is not available, run \"mix deps.get\""
      assert_received {:mix_shell, :error, [^msg]}

      assert_received {:mix_shell, :error, ["* invalidvsn (deps/invalidvsn)"]}
      assert_received {:mix_shell, :error, ["  the app file contains an invalid version: :ok"]}

      assert_received {:mix_shell, :error, ["* invalidapp (deps/invalidapp)"]}
      msg = "  the app file at \"_build/dev/lib/invalidapp/ebin/invalidapp.app\" is invalid"
      assert_received {:mix_shell, :error, [^msg]}

      # This one is compiled automatically
      refute_received {:mix_shell, :error, ["* noappfile (deps/noappfile)"]}
      refute_received {:mix_shell, :error, ["  could not find an app file at " <> _]}
    end)
  end

  ## deps.unlock

  test "unlocks all deps", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)

      Mix.Dep.Lock.write(%{git_repo: "abcdef"})
      assert Mix.Dep.Lock.read() == %{git_repo: "abcdef"}
      Mix.Tasks.Deps.Unlock.run(["--all"])
      assert Mix.Dep.Lock.read() == %{}
    end)
  end

  test "checks lock file has unused deps with --check-unused", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)

      Mix.Dep.Lock.write(%{whatever: "0.2.0", something_else: "1.2.3", ok: "0.1.0"})
      assert Mix.Dep.Lock.read() == %{whatever: "0.2.0", something_else: "1.2.3", ok: "0.1.0"}

      error = """
      Unused dependencies in mix.lock file:

        * :something_else
        * :whatever
      """

      assert_raise Mix.Error, error, fn ->
        Mix.Tasks.Deps.Unlock.run(["--check-unused"])
      end

      assert Mix.Dep.Lock.read() == %{whatever: "0.2.0", something_else: "1.2.3", ok: "0.1.0"}

      Mix.Tasks.Deps.Unlock.run(["--unused"])
      Mix.Tasks.Deps.Unlock.run(["--check-unused"])
      assert Mix.Dep.Lock.read() == %{ok: "0.1.0"}
    end)
  end

  test "unlocks unused deps", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)

      Mix.Dep.Lock.write(%{whatever: "abcdef", ok: "abcdef"})
      assert Mix.Dep.Lock.read() == %{whatever: "abcdef", ok: "abcdef"}
      Mix.Tasks.Deps.Unlock.run(["--unused"])
      assert Mix.Dep.Lock.read() == %{ok: "abcdef"}

      output = """
      Unlocked deps:
      * whatever
      """

      assert_received {:mix_shell, :info, [^output]}
    end)
  end

  test "unlocking a dep that is not locked is a no-op", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)
      Mix.Tasks.Deps.Unlock.run(["unlocked_dep"])

      assert_received {:mix_shell, :error, ["warning: unlocked_dep dependency is not locked"]}
      refute_received {:mix_shell, :info, [_]}
    end)
  end

  test "unlocks specific deps", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)

      Mix.Dep.Lock.write(%{git_repo: "abcdef", another: "hash"})
      Mix.Tasks.Deps.Unlock.run(["git_repo", "unknown"])
      assert Mix.Dep.Lock.read() == %{another: "hash"}
      error = "warning: unknown dependency is not locked"
      assert_received {:mix_shell, :error, [^error]}

      output = """
      Unlocked deps:
      * git_repo
      """

      assert_received {:mix_shell, :info, [^output]}
    end)
  end

  test "unlocks filtered deps", context do
    in_tmp(context.test, fn ->
      Mix.Project.push(DepsApp)

      Mix.Dep.Lock.write(%{git_repo: "abcdef", another: "hash", another_one: "hash"})
      Mix.Tasks.Deps.Unlock.run(["--filter", "another"])
      assert Mix.Dep.Lock.read() == %{git_repo: "abcdef"}

      output = """
      Unlocked deps:
      * another
      * another_one
      """

      assert_received {:mix_shell, :info, [^output]}
    end)
  end

  test "fails with message on missing dependencies" do
    Mix.Project.push(DepsApp)

    assert_raise Mix.Error, ~r/"mix deps\.unlock" expects dependencies as arguments/, fn ->
      Mix.Tasks.Deps.Unlock.run([])
    end
  end

  ## Deps environment

  defmodule CustomDepsEnvApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:raw_repo, "0.1.0", path: "custom/raw_repo", env: :dev}
        ]
      ]
    end
  end

  test "sets deps env to prod by default" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(RawRepoDepApp)

      Mix.Tasks.Deps.Update.run(["--all"])
      assert_received {:mix_shell, :info, [":raw_repo env is prod"]}
    end)
  end

  test "can customize environment" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CustomDepsEnvApp)

      Mix.Tasks.Deps.Update.run(["--all"])
      assert_received {:mix_shell, :info, [":raw_repo env is dev"]}
    end)
  end

  ## Nested dependencies

  defmodule ConflictDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:git_repo, "0.1.0", path: "custom/raw_repo"},
          {:bad_deps_repo, "0.1.0", path: "custom/bad_deps_repo"}
        ]
      ]
    end
  end

  defmodule DivergedDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:deps_repo, "0.1.0", path: "custom/deps_repo"},
          {:bad_deps_repo, "0.1.0", path: "custom/bad_deps_repo"}
        ]
      ]
    end
  end

  defmodule ConvergedDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:deps_repo, "0.1.0", path: "custom/deps_repo"},
          {:git_repo, ">= 0.1.0", git: MixTest.Case.fixture_path("git_repo")}
        ]
      ]
    end
  end

  defmodule OverriddenDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:bad_deps_repo, "0.1.0", path: "custom/bad_deps_repo"},
          {:git_repo, "0.1.0", git: MixTest.Case.fixture_path("git_repo"), override: true}
        ]
      ]
    end
  end

  defmodule NonOverriddenDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:bad_deps_repo, "0.1.0", path: "custom/bad_deps_repo"},
          {:git_repo, "0.1.0", git: MixTest.Case.fixture_path("git_repo")}
        ]
      ]
    end
  end

  test "fails on missing dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      assert_raise Mix.Error, ~r/Unknown dependency invalid for environment dev/, fn ->
        Mix.Tasks.Deps.Update.run(["invalid"])
      end
    end)
  end

  @overriding_msg "  the dependency git_repo in mix.exs is overriding a child dependency"

  test "fails on diverged dependencies on get/update" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ConflictDepsApp, "mix.exs")

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      assert_received {:mix_shell, :error, [@overriding_msg <> _]}

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Get.run([])
      end

      assert_received {:mix_shell, :error, [@overriding_msg <> _]}

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Update.run(["--all"])
      end

      assert_received {:mix_shell, :error, [@overriding_msg <> _]}
    end)
  end

  test "fails on diverged dependencies on check" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DivergedDepsApp)

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      assert_received {:mix_shell, :error, ["  different specs were given" <> _ = received_msg]}
      assert received_msg =~ "In custom/deps_repo/mix.exs:"

      assert received_msg =~
               "{:git_repo, \"0.1.0\", [env: :prod, git: #{inspect(fixture_path("git_repo"))}]}"
    end)
  end

  test "fails on diverged dependencies by requirement" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ConvergedDepsApp)

      File.write!("custom/deps_repo/mix.exs", """
      defmodule DepsRepo do
        use Mix.Project

        def project do
          [
            app: :deps_repo,
            version: "0.1.0",
            deps: [
              {:git_repo, "0.2.0", git: MixTest.Case.fixture_path("git_repo")}
            ]
          ]
        end
      end
      """)

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Get.run([])
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      assert_received {:mix_shell, :error, ["  the dependency git_repo 0.1.0" <> _ = msg]}
      assert msg =~ "In custom/deps_repo/mix.exs:"

      assert msg =~
               "{:git_repo, \"0.2.0\", [env: :prod, git: #{inspect(fixture_path("git_repo"))}]}"
    end)
  end

  @overriding_msg "  the dependency git_repo in custom/deps_repo/mix.exs is overriding"

  test "fails on diverged dependencies even when optional" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ConvergedDepsApp, "custom/deps_repo/mix.exs")

      File.write!("custom/deps_repo/mix.exs", """
      defmodule DepsRepo do
        use Mix.Project

        def project do
          [
            app: :deps_repo,
            version: "0.1.0",
            deps: [
              {:git_repo, git: MixTest.Case.fixture_path("bad_git_repo"), branch: "omg"}
            ]
          ]
        end
      end
      """)

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Get.run([])
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      assert_received {:mix_shell, :error, [@overriding_msg <> _]}
    end)
  end

  test "works with converged dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(ConvergedDepsApp)

      Mix.Tasks.Deps.Get.run([])
      message = "* Getting git_repo (#{fixture_path("git_repo")})"
      assert_received {:mix_shell, :info, [^message]}

      # Make sure retriever uses converger,
      # so the message appears just once
      refute_received {:mix_shell, :info, [^message]}

      Mix.Task.clear()
      Mix.Tasks.Deps.Update.run(["--all"])

      message = "* Updating git_repo (#{fixture_path("git_repo")})"
      assert_received {:mix_shell, :info, [^message]}
    end)
  after
    purge([GitRepo, GitRepo.MixProject])
  end

  test "does not check dependencies if --no-deps-check is provided" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      Mix.Tasks.Deps.Get.run([])
      File.rm_rf!("deps/ok")

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Compile.run([])
      end

      Mix.Tasks.Compile.run(["--no-deps-check"])
    end)
  end

  test "works with overridden dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(OverriddenDepsApp)

      Mix.Tasks.Deps.Get.run([])
      message = "* Getting git_repo (#{fixture_path("git_repo")})"
      assert_received {:mix_shell, :info, [^message]}

      # Make sure retriever uses converger,
      # so the message appears just once
      refute_received {:mix_shell, :info, [^message]}

      Mix.Task.clear()
      Mix.Tasks.Deps.Update.run(["--all"])

      message = "* Updating git_repo (#{fixture_path("git_repo")})"
      assert_received {:mix_shell, :info, [^message]}
    end)
  after
    purge([GitRepo, GitRepo.MixProject])
  end

  test "converged dependencies errors if not overriding" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(NonOverriddenDepsApp, "custom_mix.exs")

      assert_raise Mix.Error, fn ->
        Mix.Tasks.Deps.Loadpaths.run([])
      end

      receive do
        {:mix_shell, :error, ["  the dependency git_repo in custom_mix.exs" <> _ = msg]} ->
          assert msg =~ "In custom_mix.exs:"

          assert msg =~
                   "{:git_repo, \"0.1.0\", [env: :prod, git: #{inspect(fixture_path("git_repo"))}]}"
      after
        0 -> flunk("expected overriding error message")
      end
    end)
  after
    purge([GitRepo, GitRepo.MixProject])
  end

  test "checks if dependencies are using old Elixir version" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      Mix.Tasks.Deps.Compile.run([])
      Mix.Tasks.Deps.Loadpaths.run([])

      File.mkdir_p!("_build/dev/lib/ok/ebin")
      File.mkdir_p!("_build/dev/lib/ok/.mix")
      manifest_data = :erlang.term_to_binary({:v1, "the_future", :scm})
      File.write!("_build/dev/lib/ok/.mix/compile.elixir_scm", manifest_data)
      Mix.Task.clear()

      msg =
        "  the dependency was built with an out-of-date Erlang/Elixir version, run \"mix deps.compile\""

      Mix.Tasks.Deps.run([])
      assert_received {:mix_shell, :info, [^msg]}

      # deps.loadpaths will automatically recompile it
      Mix.Tasks.Deps.Loadpaths.run([])

      Mix.Tasks.Deps.run([])
      refute_received {:mix_shell, :info, [^msg]}
    end)
  end

  test "checks if dependencies are using old scm version" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(SuccessfulDepsApp)

      Mix.Tasks.Deps.Compile.run([])
      Mix.Tasks.Deps.Loadpaths.run([])

      File.mkdir_p!("_build/dev/lib/ok/ebin")
      File.mkdir_p!("_build/dev/lib/ok/.mix")

      manifest_data =
        :erlang.term_to_binary({1, {System.version(), :erlang.system_info(:otp_release)}, :scm})

      File.write!("_build/dev/lib/ok/.mix/compile.elixir_scm", manifest_data)
      Mix.Task.clear()

      msg = "  the dependency was built with another SCM, run \"mix deps.compile\""
      Mix.Tasks.Deps.run([])
      assert_received {:mix_shell, :info, [^msg]}

      # deps.loadpaths will automatically recompile it
      Mix.Tasks.Deps.Loadpaths.run([])

      Mix.Tasks.Deps.run([])
      refute_received {:mix_shell, :info, [^msg]}
    end)
  end

  test "checks if compile env changed" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(RawRepoDepApp)
      Mix.Tasks.Deps.Loadpaths.run([])
      assert_receive {:mix_shell, :info, ["Generated raw_repo app"]}
      assert Application.spec(:raw_repo, :vsn)

      File.mkdir_p!("config")

      File.write!("config/config.exs", """
      import Config
      config :raw_repo, :compile_env, :new_value
      """)

      Application.unload(:raw_repo)
      Mix.ProjectStack.pop()
      Mix.Task.clear()
      Mix.Project.push(RawRepoDepApp)
      purge([RawRepo])
      Mix.Tasks.Loadconfig.load_compile("config/config.exs")

      Mix.Tasks.Deps.run([])

      assert_receive {:mix_shell, :info,
                      ["  the dependency build is outdated, please run \"mix deps.compile\""]}

      Mix.Tasks.Deps.Loadpaths.run([])

      assert_receive {:mix_shell, :info, ["Generated raw_repo app"]}
      assert Application.spec(:raw_repo, :vsn)
    end)
  after
    Application.delete_env(:raw_repo, :compile_env, persistent: true)
  end

  defmodule NonCompilingDeps do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:git_repo, "0.1.0", git: MixTest.Case.fixture_path("git_repo"), compile: false}
        ]
      ]
    end
  end

  test "does not compile deps that have explicit option" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(NonCompilingDeps)

      Mix.Tasks.Deps.Compile.run([])
      refute_received {:mix_shell, :info, ["==> git_repo"]}
    end)
  end

  defmodule DupDeps do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          # Simulate dependencies gathered together from umbrella
          {:ok, "0.1.0", path: "deps/ok"},
          {:ok, "0.1.0", path: "deps/ok"}
        ]
      ]
    end
  end

  test "warns and converges duplicated deps at the same level" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(DupDeps)

      Mix.Tasks.Deps.run([])

      msg =
        "warning: the dependency :ok is duplicated at the top level, please remove one of them"

      assert_received {:mix_shell, :error, [^msg]}

      msg = "* ok 0.1.0 (deps/ok) (mix)"
      assert_received {:mix_shell, :info, [^msg]}
      refute_received {:mix_shell, :info, [^msg]}
    end)
  end

  ## deps.clean

  defmodule CleanDepsApp do
    def project do
      [
        app: :raw_sample,
        version: "0.1.0",
        deps: [
          {:git_repo, ">= 0.1.0", git: MixTest.Case.fixture_path("git_repo")},
          {:ok, ">= 2.0.0", path: "deps/ok"}
        ]
      ]
    end
  end

  test "cleans dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CleanDepsApp)

      File.mkdir_p!("_build/dev/lib/raw_sample")
      File.mkdir_p!("_build/dev/lib/git_repo")
      File.mkdir_p!("_build/test/lib/git_repo")
      File.mkdir_p!("_build/dev/lib/ok")
      File.mkdir_p!("_build/test/lib/ok")

      message =
        "\"mix deps.clean\" expects dependencies as arguments or " <>
          "an option indicating which dependencies to clean. " <>
          "The --all option will clean all dependencies while " <>
          "the --unused option cleans unused dependencies"

      assert_raise Mix.Error, message, fn ->
        Mix.Tasks.Deps.Clean.run([])
      end

      Mix.Tasks.Deps.Clean.run(["--only", "dev", "--all"])
      refute File.exists?("_build/dev/lib/git_repo")
      refute File.exists?("_build/dev/lib/ok")
      assert File.exists?("_build/test/lib/git_repo")
      assert File.exists?("_build/dev/lib/raw_sample")

      Mix.Tasks.Deps.Clean.run(["--all"])
      refute File.exists?("_build/dev/lib/git_repo")
      refute File.exists?("_build/test/lib/git_repo")
      assert File.exists?("_build/dev/lib/raw_sample")
    end)
  end

  test "cleans unused dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CleanDepsApp)

      File.mkdir_p!("_build/dev/lib/raw_sample")
      File.mkdir_p!("deps/git_repo")
      File.mkdir_p!("_build/dev/lib/git_repo")
      File.mkdir_p!("deps/git_repo_unused")
      File.mkdir_p!("_build/dev/lib/git_repo_unused")

      Mix.Tasks.Deps.Clean.run(["--unused"])
      assert File.exists?("deps/git_repo")
      assert File.exists?("_build/dev/lib/git_repo")
      refute File.exists?("deps/git_repo_unused")
      refute File.exists?("_build/dev/lib/git_repo_unused")
      assert File.exists?("_build/dev/lib/raw_sample")
    end)
  end

  test "cleans dependencies build" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CleanDepsApp)

      File.mkdir_p!("deps/raw_sample")
      File.mkdir_p!("_build/dev/lib/raw_sample")

      Mix.Tasks.Deps.Clean.run(["raw_sample", "--build"])
      assert File.exists?("deps/raw_sample")
      refute File.exists?("_build/dev/lib/raw_sample")
    end)
  end

  test "warns on invalid path on clean dependencies" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CleanDepsApp)

      File.mkdir_p!("deps/raw_sample")
      File.mkdir_p!("_build/dev/lib/raw_sample")

      Mix.Tasks.Deps.Clean.run(["raw_sample_with_a_typo"])
      assert File.exists?("deps/raw_sample")

      msg = "warning: the dependency raw_sample_with_a_typo is not present in the build directory"
      assert_received {:mix_shell, :error, [^msg]}
    end)
  end

  test "does not remove dependency source when using :path" do
    in_fixture("deps_status", fn ->
      Mix.Project.push(CleanDepsApp)

      assert File.exists?("deps/ok")

      Mix.Tasks.Deps.Clean.run(["raw_sample", "--all"])
      refute File.exists?("_build/dev/lib/ok")
      refute File.exists?("_build/test/lib/ok")
      assert File.exists?("deps/ok")
    end)
  end
end
