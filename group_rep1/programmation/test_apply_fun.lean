import .apply_fun

meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."

example : true :=
begin
  my_first_tactic,
  trivial
end
meta def my_second_tactic : tactic unit :=
tactic.trace "Hello," >> tactic.trace "World."
    example : true :=
begin
  my_second_tactic,
  trivial
end
meta def my_failing_tactic  : tactic unit := tactic.failed

meta def my_failing_tactic' : tactic unit :=
tactic.fail "This tactic failed, we apologize for the inconvenience."
example : true :=
begin
  my_failing_tactic',
  trivial
end
open tactic
/-
When chaining instructions, the first failure interrupts the process. 
However the orelse combinator,
 denoted by an infix <|> allows to try its right-hand side if its left-hand 
 side failed. The following will successfully deliver its message.
-/

meta def my_orelse : tactic unit := 
fail "this tactic fail" <|> trace "hello"

example : true := begin 
    my_orelse,
    trivial, 
    end
meta def trace_goal : tactic unit :=
 tactic.target >>= tactic.trace
example (a b  : ℤ) : a = b → (a+1 = b+1)  := begin 
    trace_goal, intro hyp, apply_fun  (λ t, 1+ t) at hyp,
    exact hyp,
    end 

