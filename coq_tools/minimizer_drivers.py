from __future__ import division
from .memoize import memoize

__all__ = ["run_binary_search"]


@memoize
def apply_as_many_times_as_possible(f, x):
    if x is None:
        return None
    fx = apply_as_many_times_as_possible(f, f(x))
    if fx is None:
        return x
    return fx


def make_states(init, step):
    init = step(init)
    while init != None:
        yield init
        init = step(init)


def binary_search(f, ls):
    start, end = 0, len(ls)
    # assumption: forall i, not f(ls[i]) -> all(map(not f, ls[i:]))
    # invariant: all(map(not f, ls[end:])) and all(map(f, ls[:start]))
    mid = (start + end) // 2
    while mid < end:
        if f(ls[mid]):
            start = mid + 1
        else:
            end = mid
        mid = (start + end) // 2
    return start - 1


def run_binary_search(initial_state, check_state, step_state, save_good_state, valid_nondefault_actions):
    """
    Runs a binary search on initial_state to find the best final state.

    - initial_state : State
        Starting point.  Must be pure (no mutation necessary)

    - check_state : State -> bool
        returns True if the state is a good state, and False if it is bad.
        If run_binary_search returns any non-none value and
        check_state is pure, then check_state is guaranteed to return
        a truthy value on the returned state.

    - step_state : State -> Maybe Action -> State
        Takes a step based on the action, or returns None if no such step
        is possible.  The action is either None, or one from
        valid_nondefault_actions.  If no step is possible, step_state
        must return None, rather than its input state (otherwise
        run_binary_search may loop).  This argument must be a pure function.

        Requirement: check_state(st) == check_state(step_state(st, None))
        assuming step_state(st, None) != None

    - save_good_state : State -> ()
        Called after every discovery of a state that check_state is happy with

    - valid_nondefault_actions : [State]
        A list or tuple of actions.  Earlier actions are assumed to be better.

    Returns the state that is "best", as determined by a lexicographic
    ordering on the actions taken, where earlier actions in
    valid_nondefault_actions are better than later ones.
    """
    valid_actions = list(valid_nondefault_actions) + [None]

    @memoize
    def is_good(state):
        return check_state(state)

    def step_none(st):
        return step_state(st, None)

    def step_default(st):
        for action in valid_actions:
            try:
                return step_state(st, action)
            except ValueError:
                pass
        return step_none(st)

    last_good = None
    cur = initial_state
    while is_good(cur) and last_good != cur:
        last_good = cur
        current_states = list(make_states(cur, step_default))
        if current_states and is_good(current_states[0]):
            idx = binary_search(is_good, current_states)
            cur = current_states[idx]
            save_good_state(cur)
        else:
            for action in valid_actions:
                try:
                    next_st = step_state(cur, action)
                except ValueError:
                    continue
                if next_st and is_good(next_st):
                    cur = next_st
                    save_good_state(cur)
                    break
    return last_good
