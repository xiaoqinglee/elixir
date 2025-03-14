# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

Code.require_file("test_helper.exs", __DIR__)

defmodule AtomTest do
  use ExUnit.Case, async: true

  doctest Atom, except: [:moduledoc]

  test "to_string/1" do
    assert "héllo" |> String.to_atom() |> Atom.to_string() == "héllo"
  end

  test "to_charlist/1" do
    assert "héllo" |> String.to_atom() |> Atom.to_charlist() == ~c"héllo"
  end
end
