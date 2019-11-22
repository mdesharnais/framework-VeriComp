theory Behaviour
  imports Main
begin

datatype 'state behaviour =
  Terminates 'state | Diverges | is_wrong: Goes_wrong 'state

end