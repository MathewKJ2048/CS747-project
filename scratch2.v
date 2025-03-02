Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint bin_to_nat (m: bin):nat :=
match m with
| B0 x => 2 * (bin_to_nat x)
| B1 x => 2 * (bin_to_nat x) + 1
| Z => 0
end.

Compute bin_to_nat (B0 (B1 Z)).