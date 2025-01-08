Require Import Nat String List. 

Import ListNotations.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint execute
  (state : string -> nat)
  (stack : list nat)
  (is : list sinstr) : list nat :=
  match is with
  | [] => stack
  | i :: is' => 
      match i with
      | SPush n => execute state (n::stack) is'
      | SLoad x => execute state (state x::stack) is'
      | SPlus =>
          match stack with
          | x1 :: x2 :: stack' =>
              execute state (x1 + x2 :: stack') is'
          | _ => stack
          end
      | SMinus =>
          match stack with
          | x1 :: x2 :: stack' =>
              execute state (x2 - x1 :: stack') is'
          | _ => stack
          end
      | SMult =>
          match stack with
          | x1 :: x2 :: stack' =>
              execute state (x1 * x2 :: stack') is'
          | _ => stack
          end
      end
  end.

Require Import imp.

Example s_execute1 :
  execute (fun _ => 0) [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. simpl. reflexivity. Qed.


Example s_execute2 :
  execute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
