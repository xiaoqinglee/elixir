# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Mix.SCM.Git do
  @behaviour Mix.SCM
  @moduledoc false

  @impl true
  def fetchable? do
    true
  end

  @impl true
  def format(opts) do
    if rev = get_opts_rev(opts) do
      "#{redact_uri(opts[:git])} - #{rev}"
    else
      redact_uri(opts[:git])
    end
  end

  @impl true
  def format_lock(opts) do
    case opts[:lock] do
      {:git, _, lock_rev, lock_opts} ->
        lock = String.slice(lock_rev, 0, 7)

        case Enum.find_value([:ref, :branch, :tag], &List.keyfind(lock_opts, &1, 0)) do
          {:ref, _} -> lock <> " (ref)"
          {key, val} -> lock <> " (#{key}: #{val})"
          nil -> lock
        end

      _ ->
        nil
    end
  end

  @impl true
  def accepts_options(_app, opts) do
    opts =
      opts
      |> Keyword.put(:checkout, opts[:dest])
      |> sparse_opts()
      |> subdir_opts()

    cond do
      gh = opts[:github] ->
        opts
        |> Keyword.delete(:github)
        |> Keyword.put(:git, "https://github.com/#{gh}.git")
        |> validate_git_options()

      opts[:git] ->
        opts
        |> validate_git_options()

      true ->
        nil
    end
  end

  @impl true
  def checked_out?(opts) do
    # Are we inside a Git repository?
    opts[:checkout]
    |> Path.join(".git/HEAD")
    |> File.regular?()
  end

  @impl true
  def lock_status(opts) do
    lock = opts[:lock]

    cond do
      lock_rev = get_lock_rev(lock, opts) ->
        File.cd!(opts[:checkout], fn ->
          %{origin: origin, rev: rev} = get_rev_info()

          if get_lock_repo(lock) == origin and lock_rev == rev do
            :ok
          else
            :mismatch
          end
        end)

      is_nil(lock) ->
        :mismatch

      true ->
        :outdated
    end
  end

  @impl true
  def equal?(opts1, opts2) do
    opts1[:git] == opts2[:git] and get_lock_opts(opts1) == get_lock_opts(opts2)
  end

  @impl true
  def managers(_opts) do
    []
  end

  @impl true
  def checkout(opts) do
    path = opts[:checkout]
    File.rm_rf!(path)
    File.mkdir_p!(opts[:dest])

    File.cd!(path, fn ->
      git!(~w[-c core.hooksPath='' init --quiet])
      git!(["--git-dir=.git", "remote", "add", "origin", opts[:git]])
      checkout(path, opts)
    end)
  end

  @impl true
  def update(opts) do
    path = opts[:checkout]
    File.cd!(path, fn -> checkout(path, opts) end)
  end

  defp checkout(_path, opts) do
    Mix.shell().print_app()

    # Set configuration
    sparse_toggle(opts)
    update_origin(opts[:git])

    # Fetch external data
    lock_rev = get_lock_rev(opts[:lock], opts)

    ["--git-dir=.git", "fetch", "--force", "--quiet"]
    |> Kernel.++(progress_switch(git_version()))
    |> Kernel.++(tags_switch(opts[:tag]))
    |> Kernel.++(depth_switch(opts[:depth]))
    |> Kernel.++(refspec_switch(opts, lock_rev || get_opts_rev(opts)))
    |> git!()

    # Migrate the Git repo
    rev = lock_rev || get_origin_opts_rev(opts) || default_branch()
    git!(["--git-dir=.git", "checkout", "--force", "--quiet", rev])

    if opts[:submodules] do
      git!(~w[-c core.hooksPath='' --git-dir=.git submodule update --init --recursive])
    end

    # Get the new repo lock
    get_lock(opts)
  end

  defp sparse_opts(opts) do
    if opts[:sparse] do
      dest = Path.join(opts[:dest], opts[:sparse])
      Keyword.put(opts, :dest, dest)
    else
      opts
    end
  end

  defp subdir_opts(opts) do
    if opts[:subdir] do
      dest = Path.join(opts[:dest], opts[:subdir])
      Keyword.put(opts, :dest, dest)
    else
      opts
    end
  end

  defp sparse_toggle(opts) do
    cond do
      sparse = opts[:sparse] ->
        check_sparse_support(git_version())
        git!(["--git-dir=.git", "config", "core.sparsecheckout", "true"])
        File.mkdir_p!(".git/info")
        File.write!(".git/info/sparse-checkout", sparse)

      File.exists?(".git/info/sparse-checkout") ->
        File.write!(".git/info/sparse-checkout", "*")
        git!(["--git-dir=.git", "read-tree", "-mu", "HEAD"])
        git!(["--git-dir=.git", "config", "core.sparsecheckout", "false"])
        File.rm(".git/info/sparse-checkout")

      true ->
        :ok
    end
  end

  @min_git_version_sparse {1, 7, 4}
  @min_git_version_depth {1, 5, 0}
  @min_git_version_progress {1, 7, 1}

  defp check_sparse_support(version) do
    ensure_feature_compatibility(version, @min_git_version_sparse, "sparse checkout")
  end

  defp check_depth_support(version) do
    ensure_feature_compatibility(version, @min_git_version_depth, "depth (shallow clone)")
  end

  defp ensure_feature_compatibility(version, required_version, feature) do
    if not (required_version <= version) do
      Mix.raise(
        "Git >= #{format_version(required_version)} is required to use #{feature}. " <>
          "You are running version #{format_version(version)}"
      )
    end
  end

  defp progress_switch(version) do
    if @min_git_version_progress <= version, do: ["--progress"], else: []
  end

  defp tags_switch(nil), do: []
  defp tags_switch(_), do: ["--tags"]

  defp depth_switch(nil), do: []

  defp depth_switch(n) when is_integer(n) and n > 0 do
    check_depth_support(git_version())
    ["--depth=#{n}"]
  end

  defp refspec_switch(_opts, nil), do: []

  defp refspec_switch(opts, rev) do
    case Keyword.take(opts, [:depth, :branch, :tag]) do
      [_ | _] -> ["origin", rev]
      _ -> []
    end
  end

  ## Helpers

  defp validate_git_options(opts) do
    opts
    |> validate_refspec()
    |> validate_depth()
  end

  defp validate_refspec(opts) do
    case Keyword.take(opts, [:branch, :ref, :tag]) do
      [] ->
        opts

      [{_refspec, value}] when is_binary(value) ->
        opts

      [{refspec, value}] ->
        Mix.raise(
          "A dependency's #{refspec} must be a string, got: #{inspect(value)}. " <>
            "Error on Git dependency: #{redact_uri(opts[:git])}"
        )

      _ ->
        Mix.raise(
          "You should specify only one of branch, ref or tag, and only once. " <>
            "Error on Git dependency: #{redact_uri(opts[:git])}"
        )
    end
  end

  @sha1_size 40

  defp validate_depth(opts) do
    case Keyword.take(opts, [:depth]) do
      [] ->
        opts

      [{:depth, depth}] when is_integer(depth) and depth > 0 ->
        ref = opts[:ref]

        if ref && byte_size(ref) < @sha1_size do
          Mix.raise(
            "When :depth is used with :ref, a full commit hash is required. " <>
              "Error on Git dependency: #{redact_uri(opts[:git])}"
          )
        end

        opts

      invalid_depth ->
        Mix.raise(
          "The depth must be a positive integer, and be specified only once, got: #{inspect(invalid_depth)}. " <>
            "Error on Git dependency: #{redact_uri(opts[:git])}"
        )
    end
  end

  defp get_lock(opts) do
    %{rev: rev} = get_rev_info()
    {:git, opts[:git], rev, get_lock_opts(opts)}
  end

  defp get_lock_repo({:git, repo, _, _}), do: repo

  defp get_lock_rev({:git, repo, lock, lock_opts}, opts) when is_binary(lock) do
    if repo == opts[:git] and lock_opts == get_lock_opts(opts) do
      lock
    end
  end

  defp get_lock_rev(_, _), do: nil

  defp get_lock_opts(opts) do
    lock_opts = Keyword.take(opts, [:branch, :ref, :tag, :sparse, :subdir, :depth])

    if opts[:submodules] do
      lock_opts ++ [submodules: true]
    else
      lock_opts
    end
  end

  defp get_opts_rev(opts) do
    opts[:branch] || opts[:ref] || opts[:tag]
  end

  defp get_origin_opts_rev(opts) do
    if branch = opts[:branch] do
      "origin/#{branch}"
    else
      opts[:ref] || opts[:tag]
    end
  end

  defp redact_uri(git) do
    case URI.parse(git) do
      %{userinfo: nil} -> git
      uri -> URI.to_string(%{uri | userinfo: "****:****"})
    end
  end

  defp get_rev_info do
    # These commands can fail and we don't want to raise.
    origin_command = ["--git-dir=.git", "config", "remote.origin.url"]
    rev_command = ["--git-dir=.git", "rev-parse", "--verify", "--quiet", "HEAD"]
    opts = cmd_opts([])

    with {origin, 0} <- System.cmd("git", origin_command, opts),
         {rev, 0} <- System.cmd("git", rev_command, opts) do
      %{origin: String.trim(origin), rev: String.trim(rev)}
    else
      _ -> %{origin: nil, rev: nil}
    end
  end

  defp update_origin(location) do
    git!(["--git-dir=.git", "config", "remote.origin.url", location])
    :ok
  end

  defp default_branch() do
    # Note: the `set-head -a` command requires the remote reference to be
    # fetched first.
    git!(["--git-dir=.git", "remote", "set-head", "origin", "-a"])
    "origin/HEAD"
  end

  defp git!(args, into \\ default_into()) do
    opts = cmd_opts(into: into, stderr_to_stdout: true)

    try do
      System.cmd("git", args, opts)
    catch
      :error, :enoent ->
        Mix.raise(
          "Error fetching/updating Git repository: the \"git\" " <>
            "executable is not available in your PATH. Please install " <>
            "Git on this machine or pass --no-deps-check if you want to " <>
            "run a previously built application on a system without Git."
        )
    else
      {response, 0} ->
        response

      {response, _} when is_binary(response) ->
        Mix.raise("Command \"git #{Enum.join(args, " ")}\" failed with reason: #{response}")

      {_, _} ->
        Mix.raise("Command \"git #{Enum.join(args, " ")}\" failed")
    end
  end

  defp default_into() do
    case Mix.shell() do
      Mix.Shell.IO -> IO.stream()
      _ -> ""
    end
  end

  # Attempt to set the current working directory by default.
  # This addresses an issue changing the working directory when executing from
  # within a secondary node since file I/O is done through the main node.
  defp cmd_opts(opts) do
    case File.cwd() do
      {:ok, cwd} -> Keyword.put(opts, :cd, cwd)
      _ -> opts
    end
  end

  # Invoked by lib/mix/test/test_helper.exs
  @doc false
  def unsupported_options do
    git_version = git_version()

    []
    |> Kernel.++(if git_version < @min_git_version_sparse, do: [:sparse], else: [])
    |> Kernel.++(if git_version < @min_git_version_depth, do: [:depth], else: [])
  end

  defp git_version do
    case Mix.State.fetch(:git_version) do
      {:ok, version} ->
        version

      :error ->
        version =
          ["--version"]
          |> git!("")
          |> parse_version()

        Mix.State.put(:git_version, version)
        version
    end
  end

  defp parse_version("git version " <> version) do
    version
    |> String.split(".")
    |> Enum.take(3)
    |> Enum.map(&to_integer/1)
    |> List.to_tuple()
  end

  defp format_version(version) do
    version |> Tuple.to_list() |> Enum.join(".")
  end

  defp to_integer(string) do
    {int, _} = Integer.parse(string)
    int
  end
end
