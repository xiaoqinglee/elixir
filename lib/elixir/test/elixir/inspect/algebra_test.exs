# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

Code.require_file("../test_helper.exs", __DIR__)

defmodule Inspect.OptsTest do
  use ExUnit.Case

  test "new" do
    opts = Inspect.Opts.new(limit: 13, pretty: true)
    assert opts.limit == 13
    assert opts.pretty
  end

  test "default_inspect_fun" do
    assert Inspect.Opts.default_inspect_fun() == (&Inspect.inspect/2)

    assert Inspect.Opts.default_inspect_fun(fn
             :rewrite_atom, _ -> "rewritten_atom"
             value, opts -> Inspect.inspect(value, opts)
           end) == :ok

    assert inspect(:rewrite_atom) == "rewritten_atom"
  after
    Inspect.Opts.default_inspect_fun(&Inspect.inspect/2)
  end
end

defmodule Inspect.AlgebraTest do
  use ExUnit.Case, async: true

  doctest Inspect.Algebra

  import Inspect.Algebra

  defp render(doc, limit) do
    doc |> group() |> format(limit) |> IO.iodata_to_binary()
  end

  test "empty doc" do
    # Consistent with definitions
    assert empty() == []

    # Consistent formatting
    assert render(empty(), 80) == ""
  end

  test "strict break doc" do
    # Consistent with definitions
    assert break("break") == {:doc_break, "break", :strict}
    assert break("") == {:doc_break, "", :strict}

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> break(42) end

    # Consistent formatting
    assert render(break("_"), 80) == "_"
    assert render(glue("foo", " ", glue("bar", " ", "baz")), 10) == "foo\nbar\nbaz"
  end

  test "flex break doc" do
    # Consistent with definitions
    assert flex_break("break") == {:doc_break, "break", :flex}
    assert flex_break("") == {:doc_break, "", :flex}

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> flex_break(42) end

    # Consistent formatting
    assert render(flex_break("_"), 80) == "_"
    assert render(flex_glue("foo", " ", flex_glue("bar", " ", "baz")), 10) == "foo bar\nbaz"
  end

  test "glue doc" do
    # Consistent with definitions
    assert glue("a", "->", "b") == ["a", {:doc_break, "->", :strict} | "b"]
    assert glue("a", "b") == glue("a", " ", "b")

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> glue("a", 42, "b") end
  end

  test "flex glue doc" do
    # Consistent with definitions
    assert flex_glue("a", "->", "b") ==
             ["a", {:doc_break, "->", :flex} | "b"]

    assert flex_glue("a", "b") == flex_glue("a", " ", "b")

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> flex_glue("a", 42, "b") end
  end

  test "binary doc" do
    assert render("_", 80) == "_"
  end

  test "string doc" do
    # Consistent with definitions
    assert string("ólá") == {:doc_string, "ólá", 3}

    # Counts graphemes
    doc = glue(string("olá"), " ", string("mundo"))
    assert render(doc, 9) == "olá mundo"
  end

  test "space doc" do
    # Consistent with definitions
    assert space("a", "b") == ["a", " " | "b"]
  end

  test "always nest doc" do
    # Consistent with definitions
    assert nest(empty(), 1) == {:doc_nest, empty(), 1, :always}
    assert nest(empty(), 0) == []

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> nest("foo", empty()) end

    # Consistent formatting
    assert render(nest("a", 1), 80) == "a"
    assert render(nest(glue("a", "b"), 1), 2) == "a\n b"
    assert render(nest(line("a", "b"), 1), 20) == "a\n b"
  end

  test "break nest doc" do
    # Consistent with definitions
    assert nest(empty(), 1, :break) == {:doc_nest, empty(), 1, :break}
    assert nest(empty(), 0, :break) == []

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> nest("foo", empty(), :break) end

    # Consistent formatting
    assert render(nest("a", 1, :break), 80) == "a"
    assert render(nest(glue("a", "b"), 1, :break), 2) == "a\n b"
    assert render(nest(line("a", "b"), 1, :break), 20) == "a\nb"
  end

  test "cursor nest doc" do
    # Consistent with definitions
    assert nest(empty(), :cursor) == {:doc_nest, empty(), :cursor, :always}

    # Consistent formatting
    assert render(nest("a", :cursor), 80) == "a"
    assert render(concat("prefix ", nest(glue("a", "b"), :cursor)), 2) == "prefix a\n       b"
    assert render(concat("prefix ", nest(line("a", "b"), :cursor)), 2) == "prefix a\n       b"
  end

  test "reset nest doc" do
    # Consistent with definitions
    assert nest(empty(), :reset) == {:doc_nest, empty(), :reset, :always}

    # Consistent formatting
    assert render(nest("a", :reset), 80) == "a"
    assert render(nest(nest(glue("a", "b"), :reset), 10), 2) == "a\nb"
    assert render(nest(nest(line("a", "b"), :reset), 10), 2) == "a\nb"
  end

  test "color doc" do
    # Consistent with definitions
    opts = %Inspect.Opts{}
    assert color_doc(empty(), :atom, opts) == empty()

    opts = %Inspect.Opts{syntax_colors: [regex: :red]}
    assert color_doc(empty(), :atom, opts) == empty()

    opts = %Inspect.Opts{syntax_colors: [atom: :red]}
    doc1 = {:doc_color, "Hi", IO.ANSI.red()}
    doc2 = {:doc_color, empty(), IO.ANSI.reset()}
    assert color_doc("Hi", :atom, opts) == concat(doc1, doc2)

    opts = %Inspect.Opts{syntax_colors: [reset: :red]}
    assert color_doc(empty(), :atom, opts) == empty()

    opts = %Inspect.Opts{syntax_colors: [number: :cyan, reset: :red]}
    doc1 = {:doc_color, "123", IO.ANSI.cyan()}
    doc2 = {:doc_color, empty(), IO.ANSI.red()}
    assert color_doc("123", :number, opts) == concat(doc1, doc2)

    # Consistent formatting
    opts = %Inspect.Opts{syntax_colors: [atom: :cyan]}
    assert render(glue(color_doc("AA", :atom, opts), "BB"), 5) == "\e[36mAA\e[0m BB"
    assert render(glue(color_doc("AA", :atom, opts), "BB"), 3) == "\e[36mAA\e[0m\nBB"
    assert render(glue("AA", color_doc("BB", :atom, opts)), 6) == "AA \e[36mBB\e[0m"
  end

  test "line doc" do
    # Consistent with definitions
    assert line("a", "b") == ["a", :doc_line | "b"]

    # Consistent formatting
    assert render(line(glue("aaa", "bbb"), glue("ccc", "ddd")), 10) == "aaa bbb\nccc ddd"
  end

  test "group doc" do
    # Consistent with definitions
    assert group("ab") == {:doc_group, "ab", :normal}
    assert group(empty()) == {:doc_group, empty(), :normal}

    # Consistent formatting
    doc = concat(glue(glue(glue("hello", "a"), "b"), "c"), "d")
    assert render(group(doc), 5) == "hello\na\nb\ncd"
  end

  test "group modes doc" do
    doc = glue(glue("hello", "a"), "b")
    assert render(doc, 10) == "hello a b"

    assert render(doc |> glue("c") |> group(), 10) ==
             "hello\na\nb\nc"

    assert render(doc |> group() |> glue("c") |> group() |> glue("d"), 10) ==
             "hello a b\nc\nd"

    assert render(doc |> group(:optimistic) |> glue("c") |> group() |> glue("d"), 10) ==
             "hello\na\nb c d"

    assert render(doc |> group(:optimistic) |> glue("c") |> group(:pessimistic) |> glue("d"), 10) ==
             "hello\na\nb c\nd"
  end

  test "no limit doc" do
    doc = no_limit(group(glue(glue("hello", "a"), "b")))
    assert render(doc, 5) == "hello a b"
    assert render(doc, :infinity) == "hello a b"
  end

  test "collapse lines" do
    # Consistent with definitions
    assert collapse_lines(3) == {:doc_collapse, 3}

    # Wrong argument type
    assert_raise FunctionClauseError, fn -> collapse_lines(0) end
    assert_raise FunctionClauseError, fn -> collapse_lines(empty()) end

    # Consistent formatting
    doc = concat([collapse_lines(2), line(), line(), line()])
    assert render(doc, 10) == "\n\n"
    assert render(nest(doc, 2), 10) == "\n\n  "

    doc = concat([collapse_lines(2), line(), line()])
    assert render(doc, 10) == "\n\n"
    assert render(nest(doc, 2), 10) == "\n\n  "

    doc = concat([collapse_lines(2), line()])
    assert render(doc, 10) == "\n"
    assert render(nest(doc, 2), 10) == "\n  "

    doc = concat([collapse_lines(2), line(), "", line(), "", line()])
    assert render(doc, 10) == "\n\n"
    assert render(nest(doc, 2), 10) == "\n\n  "

    doc = concat([collapse_lines(2), line(), "foo", line(), "bar", line()])
    assert render(doc, 10) == "\nfoo\nbar\n"
    assert render(nest(doc, 2), 10) == "\n  foo\n  bar\n  "
  end

  test "force doc and cancel doc" do
    # Consistent with definitions
    assert force_unfit("ab") == {:doc_force, "ab"}
    assert force_unfit(empty()) == {:doc_force, empty()}

    # Consistent formatting
    doc = force_unfit(glue(glue("hello", "a"), "b"))
    assert render(doc, 20) == "hello\na\nb"

    assert render(doc |> glue("c") |> group(), 20) ==
             "hello\na\nb\nc"

    assert render(doc |> group(:optimistic) |> glue("c") |> group() |> glue("d"), 20) ==
             "hello\na\nb c d"

    assert render(doc |> group(:optimistic) |> glue("c") |> group(:pessimistic) |> glue("d"), 20) ==
             "hello\na\nb c\nd"
  end

  test "formatting groups with lines" do
    doc = line(glue("a", "b"), glue("hello", "world"))
    assert render(group(doc), 5) == "a\nb\nhello\nworld"
    assert render(group(doc), 100) == "a b\nhello world"
  end

  test "formatting with infinity" do
    str = String.duplicate("x", 50)
    colon = ";"

    doc =
      str
      |> glue(colon, str)
      |> glue(colon, str)
      |> glue(colon, str)
      |> glue(colon, str)
      |> group()

    assert render(doc, :infinity) ==
             str <> colon <> str <> colon <> str <> colon <> str <> colon <> str
  end

  test "formatting container_doc with empty" do
    sm = &container_doc("[", &1, "]", %Inspect.Opts{}, fn d, _ -> d end, separator: ",")

    assert sm.([]) |> render(80) == "[]"
    assert sm.([empty()]) |> render(80) == "[]"
    assert sm.([empty(), empty()]) |> render(80) == "[]"
    assert sm.(["a"]) |> render(80) == "[a]"
    assert sm.(["a", empty()]) |> render(80) == "[a]"
    assert sm.([empty(), "a"]) |> render(80) == "[a]"
    assert sm.(["a", empty(), "b"]) |> render(80) == "[a, b]"
    assert sm.([empty(), "a", "b"]) |> render(80) == "[a, b]"
    assert sm.(["a", "b", empty()]) |> render(80) == "[a, b]"
    assert sm.(["a", "b" | "c"]) |> render(80) == "[a, b | c]"
    assert sm.(["a" | "b"]) |> render(80) == "[a | b]"
    assert sm.(["a" | empty()]) |> render(80) == "[a]"
    assert sm.([empty() | "b"]) |> render(80) == "[b]"
  end

  test "formatting container_doc with empty and limit" do
    opts = %Inspect.Opts{limit: 2}
    value = ["a", empty(), "b"]

    assert container_doc("[", value, "]", opts, fn d, _ -> d end, separator: ",") |> render(80) ==
             "[a, b]"
  end
end
