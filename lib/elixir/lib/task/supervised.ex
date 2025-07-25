# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team
# SPDX-FileCopyrightText: 2012 Plataformatec

defmodule Task.Supervised do
  @moduledoc false
  @ref_timeout 5000

  def start(owner, callers, fun) do
    {:ok, spawn(__MODULE__, :noreply, [owner, get_ancestors(), callers, fun])}
  end

  def start_link(owner, callers, fun) do
    {:ok, spawn_link(__MODULE__, :noreply, [owner, get_ancestors(), callers, fun])}
  end

  def start_link(owner, monitor) do
    {:ok, spawn_link(__MODULE__, :reply, [owner, get_ancestors(), monitor])}
  end

  def reply({_, _, owner_pid} = owner, ancestors, monitor) do
    put_ancestors(ancestors)

    case monitor do
      :monitor ->
        mref = Process.monitor(owner_pid)
        reply(owner, owner_pid, mref, @ref_timeout)

      :nomonitor ->
        reply(owner, owner_pid, nil, :infinity)
    end
  end

  defp reply(owner, owner_pid, mref, timeout) do
    receive do
      {^owner_pid, ref, reply_to, callers, mfa} ->
        put_initial_call(mfa)
        put_callers(callers)
        _ = is_reference(mref) && Process.demonitor(mref, [:flush])
        send(reply_to, {ref, invoke_mfa(owner, mfa)})

      {:DOWN, ^mref, _, _, reason} ->
        exit({:shutdown, reason})
    after
      # There is a race condition on this operation when working across
      # node that manifests if a "Task.Supervisor.async/2" call is made
      # while the supervisor is busy spawning previous tasks.
      #
      # Imagine the following workflow:
      #
      # 1. The nodes disconnect
      # 2. The async call fails and is caught, the calling process does not exit
      # 3. The task is spawned and links to the calling process, causing the nodes to reconnect
      # 4. The calling process has not exited and so does not send its monitor reference
      # 5. The spawned task waits forever for the monitor reference so it can begin
      #
      # We have solved this by specifying a timeout of 5000 milliseconds.
      # Given no work is done in the client between the task start and
      # sending the reference, 5000 should be enough to not raise false
      # negatives unless the nodes are indeed not available.
      #
      # The same situation could occur with "Task.Supervisor.async_nolink/2",
      # except a monitor is used instead of a link.
      timeout ->
        exit(:timeout)
    end
  end

  def noreply(owner, ancestors, callers, mfa) do
    put_initial_call(mfa)
    put_ancestors(ancestors)
    put_callers(callers)
    invoke_mfa(owner, mfa)
  end

  defp get_ancestors() do
    case :erlang.get(:"$ancestors") do
      ancestors when is_list(ancestors) -> [self() | ancestors]
      _ -> [self()]
    end
  end

  defp put_ancestors(ancestors) do
    Process.put(:"$ancestors", ancestors)
  end

  defp put_callers(callers) do
    Process.put(:"$callers", callers)
  end

  defp put_initial_call(mfa) do
    Process.put(:"$initial_call", get_initial_call(mfa))
  end

  defp get_initial_call({:erlang, :apply, [fun, []]}) when is_function(fun, 0) do
    :erlang.fun_info_mfa(fun)
  end

  defp get_initial_call({mod, fun, args}) do
    {mod, fun, length(args)}
  end

  defp invoke_mfa(owner, {module, fun, args} = mfa) do
    try do
      apply(module, fun, args)
    catch
      :exit, value
      when value == :normal
      when value == :shutdown
      when tuple_size(value) == 2 and elem(value, 0) == :shutdown ->
        :erlang.raise(:exit, value, __STACKTRACE__)

      kind, value ->
        {fun, args} = get_running(mfa)

        :logger.error(
          %{
            label: {Task.Supervisor, :terminating},
            report: %{
              name: self(),
              starter: get_from(owner),
              function: fun,
              args: args,
              reason: {log_value(kind, value), __STACKTRACE__},
              # TODO use Process.get_label/0 when we require Erlang/OTP 27+
              process_label: Process.get(:"$process_label", :undefined)
            }
          },
          %{
            domain: [:otp, :elixir],
            error_logger: %{tag: :error_msg},
            report_cb: &__MODULE__.format_report/1,
            callers: Process.get(:"$callers")
          }
        )

        :erlang.raise(:exit, exit_reason(kind, value, __STACKTRACE__), __STACKTRACE__)
    end
  end

  defp exit_reason(:error, reason, stacktrace), do: {reason, stacktrace}
  defp exit_reason(:exit, reason, _stacktrace), do: reason
  defp exit_reason(:throw, reason, stacktrace), do: {{:nocatch, reason}, stacktrace}

  defp log_value(:throw, value), do: {:nocatch, value}
  defp log_value(_, value), do: value

  @doc false
  def format_report(%{
        label: {Task.Supervisor, :terminating},
        report: %{
          name: name,
          starter: starter,
          function: fun,
          args: args,
          reason: reason,
          process_label: process_label
        }
      }) do
    message =
      ~c"** Started from ~p~n" ++
        ~c"** When function  == ~p~n" ++
        ~c"**      arguments == ~p~n" ++ ~c"** Reason for termination == ~n" ++ ~c"** ~p~n"

    terms = [name, fun, args, get_reason(reason)]

    {message, terms} =
      case process_label do
        :undefined -> {message, terms}
        _ -> {~c"** Process Label == ~p~n" ++ message, [process_label | terms]}
      end

    message =
      ~c"** Task ~p terminating~n" ++ message

    {message, [starter | terms]}
  end

  defp get_from({node, pid_or_name, _pid}) when node == node(), do: pid_or_name
  defp get_from({node, name, _pid}) when is_atom(name), do: {node, name}
  defp get_from({_node, _name, pid}), do: pid

  defp get_running({:erlang, :apply, [fun, []]}) when is_function(fun, 0), do: {fun, []}
  defp get_running({mod, fun, args}), do: {Function.capture(mod, fun, length(args)), args}

  defp get_reason({:undef, [{mod, fun, args, _info} | _] = stacktrace} = reason)
       when is_atom(mod) and is_atom(fun) do
    cond do
      not Code.loaded?(mod) ->
        {:"module could not be loaded", stacktrace}

      is_list(args) and not function_exported?(mod, fun, length(args)) ->
        {:"function not exported", stacktrace}

      is_integer(args) and not function_exported?(mod, fun, args) ->
        {:"function not exported", stacktrace}

      true ->
        reason
    end
  end

  defp get_reason(reason) do
    reason
  end

  ## Stream

  def validate_stream_options(options) do
    max_concurrency = Keyword.get_lazy(options, :max_concurrency, &System.schedulers_online/0)
    on_timeout = Keyword.get(options, :on_timeout, :exit)
    timeout = Keyword.get(options, :timeout, 5000)
    ordered = Keyword.get(options, :ordered, true)
    zip_input_on_exit = Keyword.get(options, :zip_input_on_exit, false)

    if not (is_integer(max_concurrency) and max_concurrency > 0) do
      raise ArgumentError, ":max_concurrency must be an integer greater than zero"
    end

    if on_timeout not in [:exit, :kill_task] do
      raise ArgumentError, ":on_timeout must be either :exit or :kill_task"
    end

    if not ((is_integer(timeout) and timeout >= 0) or timeout == :infinity) do
      raise ArgumentError, ":timeout must be either a positive integer or :infinity"
    end

    %{
      max_concurrency: max_concurrency,
      on_timeout: on_timeout,
      timeout: timeout,
      ordered: ordered,
      zip_input_on_exit: zip_input_on_exit
    }
  end

  def stream(enumerable, acc, reducer, callers, mfa, options, spawn) when is_map(options) do
    next = &Enumerable.reduce(enumerable, &1, fn x, acc -> {:suspend, [x | acc]} end)
    parent = self()

    {:trap_exit, trap_exit?} = Process.info(self(), :trap_exit)

    # Start a process responsible for spawning processes and translating "down"
    # messages. This process will trap exits if the current process is trapping
    # exit, or it won't trap exits otherwise.
    spawn_opts = [:link, :monitor]

    {monitor_pid, monitor_ref} =
      Process.spawn(
        fn -> stream_monitor(parent, spawn, trap_exit?, options.timeout) end,
        spawn_opts
      )

    # Now that we have the pid of the "monitor" process and the reference of the
    # monitor we use to monitor such process, we can inform the monitor process
    # about our reference to it.
    send(monitor_pid, {parent, monitor_ref})

    config =
      Map.merge(
        options,
        %{
          reducer: reducer,
          monitor_pid: monitor_pid,
          monitor_ref: monitor_ref,
          callers: callers,
          mfa: mfa
        }
      )

    stream_reduce(
      acc,
      options.max_concurrency,
      _spawned = 0,
      _delivered = 0,
      _waiting = %{},
      next,
      config
    )
  end

  defp stream_reduce({:halt, acc}, _max, _spawned, _delivered, _waiting, next, config) do
    stream_close(config)
    is_function(next) && next.({:halt, []})
    {:halted, acc}
  end

  defp stream_reduce({:suspend, acc}, max, spawned, delivered, waiting, next, config) do
    continuation = &stream_reduce(&1, max, spawned, delivered, waiting, next, config)
    {:suspended, acc, continuation}
  end

  # All spawned, all delivered, next is :done.
  defp stream_reduce({:cont, acc}, _max, spawned, delivered, _waiting, next, config)
       when spawned == delivered and next == :done do
    stream_close(config)
    {:done, acc}
  end

  # No more tasks to spawn because max == 0 or next is :done. We wait for task
  # responses or tasks going down.
  defp stream_reduce({:cont, acc}, max, spawned, delivered, waiting, next, config)
       when max == 0
       when next == :done do
    %{
      monitor_pid: monitor_pid,
      monitor_ref: monitor_ref,
      timeout: timeout,
      on_timeout: on_timeout,
      zip_input_on_exit: zip_input_on_exit?,
      ordered: ordered?
    } = config

    receive do
      # The task at position "position" replied with "value". We put the
      # response in the "waiting" map and do nothing, since we'll only act on
      # this response when the replying task dies (we'll see this in the :down
      # message).
      {{^monitor_ref, position}, reply} ->
        %{^position => {pid, :running, _element}} = waiting
        waiting = Map.put(waiting, position, {pid, {:ok, reply}})
        stream_reduce({:cont, acc}, max, spawned, delivered, waiting, next, config)

      # The task at position "position" died for some reason. We check if it
      # replied already (then the death is peaceful) or if it's still running
      # (then the reply from this task will be {:exit, reason}). This message is
      # sent to us by the monitor process, not by the dying task directly.
      {kind, {^monitor_ref, position}, reason}
      when kind in [:down, :timed_out] ->
        result =
          case waiting do
            # If the task replied, we don't care whether it went down for timeout
            # or for normal reasons.
            %{^position => {_, {:ok, _} = ok}} ->
              ok

            # If the task exited by itself before replying, we emit {:exit, reason}.
            %{^position => {_, :running, element}}
            when kind == :down ->
              if zip_input_on_exit?, do: {:exit, {element, reason}}, else: {:exit, reason}

            # If the task timed out before replying, we either exit (on_timeout: :exit)
            # or emit {:exit, :timeout} (on_timeout: :kill_task) (note the task is already
            # dead at this point).
            %{^position => {_, :running, element}}
            when kind == :timed_out ->
              if on_timeout == :exit do
                stream_cleanup_inbox(monitor_pid, monitor_ref)
                exit({:timeout, {__MODULE__, :stream, [timeout]}})
              else
                if zip_input_on_exit?, do: {:exit, {element, :timeout}}, else: {:exit, :timeout}
              end
          end

        if ordered? do
          waiting = Map.put(waiting, position, {:done, result})
          stream_deliver({:cont, acc}, max + 1, spawned, delivered, waiting, next, config)
        else
          pair = deliver_now(result, acc, next, config)
          waiting = Map.delete(waiting, position)
          stream_reduce(pair, max + 1, spawned, delivered + 1, waiting, next, config)
        end

      # The monitor process died. We just cleanup the messages from the monitor
      # process and exit.
      {:DOWN, ^monitor_ref, _, _, reason} ->
        stream_cleanup_inbox(monitor_pid, monitor_ref)
        exit({reason, {__MODULE__, :stream, [timeout]}})
    end
  end

  defp stream_reduce({:cont, acc}, max, spawned, delivered, waiting, next, config) do
    try do
      next.({:cont, []})
    catch
      kind, reason ->
        stream_close(config)
        :erlang.raise(kind, reason, __STACKTRACE__)
    else
      {:suspended, [value], next} ->
        waiting = stream_spawn(value, spawned, waiting, config)
        stream_reduce({:cont, acc}, max - 1, spawned + 1, delivered, waiting, next, config)

      {_, [value]} ->
        waiting = stream_spawn(value, spawned, waiting, config)
        stream_reduce({:cont, acc}, max - 1, spawned + 1, delivered, waiting, :done, config)

      {_, []} ->
        stream_reduce({:cont, acc}, max, spawned, delivered, waiting, :done, config)
    end
  end

  defp deliver_now(reply, acc, next, config) do
    %{reducer: reducer} = config

    try do
      reducer.(reply, acc)
    catch
      kind, reason ->
        is_function(next) && next.({:halt, []})
        stream_close(config)
        :erlang.raise(kind, reason, __STACKTRACE__)
    end
  end

  defp stream_deliver({:suspend, acc}, max, spawned, delivered, waiting, next, config) do
    continuation = &stream_deliver(&1, max, spawned, delivered, waiting, next, config)
    {:suspended, acc, continuation}
  end

  defp stream_deliver({:halt, acc}, max, spawned, delivered, waiting, next, config) do
    stream_reduce({:halt, acc}, max, spawned, delivered, waiting, next, config)
  end

  defp stream_deliver({:cont, acc}, max, spawned, delivered, waiting, next, config) do
    %{reducer: reducer} = config

    case waiting do
      %{^delivered => {:done, reply}} ->
        try do
          reducer.(reply, acc)
        catch
          kind, reason ->
            is_function(next) && next.({:halt, []})
            stream_close(config)
            :erlang.raise(kind, reason, __STACKTRACE__)
        else
          pair ->
            waiting = Map.delete(waiting, delivered)
            stream_deliver(pair, max, spawned, delivered + 1, waiting, next, config)
        end

      %{} ->
        stream_reduce({:cont, acc}, max, spawned, delivered, waiting, next, config)
    end
  end

  defp stream_close(%{monitor_pid: monitor_pid, monitor_ref: monitor_ref, timeout: timeout}) do
    send(monitor_pid, {:stop, monitor_ref})

    receive do
      {:DOWN, ^monitor_ref, _, _, :normal} ->
        stream_cleanup_inbox(monitor_pid, monitor_ref)
        :ok

      {:DOWN, ^monitor_ref, _, _, reason} ->
        stream_cleanup_inbox(monitor_pid, monitor_ref)
        exit({reason, {__MODULE__, :stream, [timeout]}})
    end
  end

  defp stream_cleanup_inbox(monitor_pid, monitor_ref) do
    receive do
      {:EXIT, ^monitor_pid, _} -> stream_cleanup_inbox(monitor_ref)
    after
      0 -> stream_cleanup_inbox(monitor_ref)
    end
  end

  defp stream_cleanup_inbox(monitor_ref) do
    receive do
      {{^monitor_ref, _}, _} ->
        stream_cleanup_inbox(monitor_ref)

      {kind, {^monitor_ref, _}, _} when kind in [:down, :timed_out] ->
        stream_cleanup_inbox(monitor_ref)
    after
      0 ->
        :ok
    end
  end

  # This function spawns a task for the given "value", and puts the pid of this
  # new task in the map of "waiting" tasks, which is returned.
  defp stream_spawn(value, spawned, waiting, config) do
    %{
      monitor_pid: monitor_pid,
      monitor_ref: monitor_ref,
      timeout: timeout,
      callers: callers,
      mfa: mfa,
      zip_input_on_exit: zip_input_on_exit?
    } = config

    send(monitor_pid, {:spawn, spawned})

    receive do
      {:spawned, {^monitor_ref, ^spawned}, pid} ->
        mfa_with_value = normalize_mfa_with_arg(mfa, value)
        send(pid, {self(), {monitor_ref, spawned}, self(), callers, mfa_with_value})
        stored_value = if zip_input_on_exit?, do: value, else: nil
        Map.put(waiting, spawned, {pid, :running, stored_value})

      {:max_children, ^monitor_ref} ->
        stream_close(config)

        raise """
        reached the maximum number of tasks for this task supervisor. The maximum number \
        of tasks that are allowed to run at the same time under this supervisor can be \
        configured with the :max_children option passed to Task.Supervisor.start_link/1. When \
        using async_stream or async_stream_nolink, make sure to configure :max_concurrency to \
        be lower or equal to :max_children and pay attention to whether other tasks are also \
        spawned under the same task supervisor.\
        """

      {:DOWN, ^monitor_ref, _, ^monitor_pid, reason} ->
        stream_cleanup_inbox(monitor_pid, monitor_ref)
        exit({reason, {__MODULE__, :stream, [timeout]}})
    end
  end

  defp stream_monitor(parent_pid, spawn, trap_exit?, timeout) do
    Process.flag(:trap_exit, trap_exit?)
    parent_ref = Process.monitor(parent_pid)

    # Let's wait for the parent process to tell this process the monitor ref
    # it's using to monitor this process. If the parent process dies while this
    # process waits, this process dies with the same reason.
    receive do
      {^parent_pid, monitor_ref} ->
        config = %{
          parent_pid: parent_pid,
          parent_ref: parent_ref,
          spawn: spawn,
          monitor_ref: monitor_ref,
          timeout: timeout
        }

        stream_monitor_loop(_running_tasks = %{}, config)

      {:DOWN, ^parent_ref, _, _, reason} ->
        exit(reason)
    end
  end

  defp stream_monitor_loop(running_tasks, config) do
    %{
      spawn: spawn,
      parent_pid: parent_pid,
      monitor_ref: monitor_ref,
      timeout: timeout
    } = config

    receive do
      # The parent process is telling us to spawn a new task to process
      # "value". We spawn it and notify the parent about its pid.
      {:spawn, position} ->
        case spawn.() do
          {:ok, type, pid} ->
            ref = Process.monitor(pid)

            # Schedule a timeout message to ourselves, unless the timeout was set to :infinity
            timer_ref =
              case timeout do
                :infinity -> nil
                timeout -> Process.send_after(self(), {:timeout, {monitor_ref, ref}}, timeout)
              end

            send(parent_pid, {:spawned, {monitor_ref, position}, pid})

            running_tasks =
              Map.put(running_tasks, ref, %{
                position: position,
                type: type,
                pid: pid,
                timer_ref: timer_ref,
                timed_out?: false
              })

            stream_monitor_loop(running_tasks, config)

          {:error, :max_children} ->
            send(parent_pid, {:max_children, monitor_ref})
            stream_waiting_for_stop_loop(running_tasks, config)
        end

      # One of the spawned processes went down. We inform the parent process of
      # this and keep going.
      {:DOWN, ref, _, _, reason} when is_map_key(running_tasks, ref) ->
        {task, running_tasks} = Map.pop(running_tasks, ref)
        %{position: position, timer_ref: timer_ref, timed_out?: timed_out?} = task

        if timer_ref != nil do
          :ok = Process.cancel_timer(timer_ref, async: true, info: false)
        end

        message_kind = if(timed_out?, do: :timed_out, else: :down)
        send(parent_pid, {message_kind, {monitor_ref, position}, reason})
        stream_monitor_loop(running_tasks, config)

      # One of the spawned processes timed out. We kill that process here
      # regardless of the value of :on_timeout. We then send a message to the
      # parent process informing it that a task timed out, and the parent
      # process decides what to do.
      {:timeout, {^monitor_ref, ref}} ->
        running_tasks =
          case running_tasks do
            %{^ref => %{pid: pid, timed_out?: false} = task_info} ->
              unlink_and_kill(pid)
              Map.put(running_tasks, ref, %{task_info | timed_out?: true})

            _other ->
              running_tasks
          end

        stream_monitor_loop(running_tasks, config)

      {:EXIT, _, _} ->
        stream_monitor_loop(running_tasks, config)

      other ->
        handle_stop_or_parent_down(other, running_tasks, config)
        stream_monitor_loop(running_tasks, config)
    end
  end

  defp stream_waiting_for_stop_loop(running_tasks, config) do
    receive do
      message ->
        handle_stop_or_parent_down(message, running_tasks, config)
        stream_waiting_for_stop_loop(running_tasks, config)
    end
  end

  # The parent process is telling us to stop because the stream is being
  # closed. In this case, we forcibly kill all spawned processes and then
  # exit gracefully ourselves.
  defp handle_stop_or_parent_down(
         {:stop, monitor_ref},
         running_tasks,
         %{monitor_ref: monitor_ref}
       ) do
    Process.flag(:trap_exit, true)

    for {_ref, %{pid: pid}} <- running_tasks, do: Process.exit(pid, :kill)

    for {ref, _task} <- running_tasks do
      receive do
        {:DOWN, ^ref, _, _, _} -> :ok
      end
    end

    exit(:normal)
  end

  # The parent process went down with a given reason. We kill all the
  # spawned processes (that are also linked) with the same reason, and then
  # exit ourselves with the same reason.
  defp handle_stop_or_parent_down(
         {:DOWN, parent_ref, _, _, reason},
         running_tasks,
         %{parent_ref: parent_ref}
       ) do
    for {_ref, %{type: :link, pid: pid}} <- running_tasks do
      Process.exit(pid, reason)
    end

    exit(reason)
  end

  # We ignore all other messages.
  defp handle_stop_or_parent_down(_other, _running_tasks, _config) do
    :ok
  end

  defp unlink_and_kill(pid) do
    caller = self()
    ref = make_ref()

    enforcer =
      spawn(fn ->
        mon = Process.monitor(caller)

        receive do
          {:done, ^ref} -> :ok
          {:DOWN, ^mon, _, _, _} -> Process.exit(pid, :kill)
        end
      end)

    Process.unlink(pid)
    Process.exit(pid, :kill)
    send(enforcer, {:done, ref})
  end

  defp normalize_mfa_with_arg({mod, fun, args}, arg), do: {mod, fun, [arg | args]}
  defp normalize_mfa_with_arg(fun, arg), do: {:erlang, :apply, [fun, [arg]]}
end
