# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

# Manifest file where we treat Erlang/OTP, Elixir and SCMs as a dependency.
defmodule Mix.Dep.ElixirSCM do
  @moduledoc false
  @manifest "compile.elixir_scm"
  @manifest_vsn 1

  def manifest(manifest_path \\ Mix.Project.manifest_path()) do
    Path.join(manifest_path, @manifest)
  end

  def update(manifest_path \\ Mix.Project.manifest_path(), scm) do
    File.mkdir_p!(manifest_path)

    manifest_data =
      {@manifest_vsn, {System.version(), :erlang.system_info(:otp_release)}, scm}
      |> :erlang.term_to_binary()

    File.write!(manifest(manifest_path), manifest_data)
  end

  def read(manifest_path \\ Mix.Project.manifest_path()) do
    case File.read(manifest(manifest_path)) do
      {:ok, contents} ->
        try do
          {@manifest_vsn, vsn, scm} = :erlang.binary_to_term(contents)
          {:ok, vsn, scm}
        rescue
          _ -> {:ok, {"1.0.0", ~c"17"}, nil}
        end

      _ ->
        :error
    end
  end
end
