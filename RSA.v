Inductive N : Type :=
| O
| S (n: N).

Fixpoint add(a b : N): N :=
match a with
| O => b
| S x => add x (S b)
end.


Compute add (S (S O)) (S O).

Fixpoint mult(a b : N): N :=
match a with
| O => O
| S x => add b (mult x b)
end.

Definition one := S O.

(*a^b*)
Fixpoint exp(a b : N): N :=
match b with
| O => one
| S x => mult a (exp a x)
end.

Fixpoint min(a b : N): N :=
match a with
| O => O
| S x => (
	match b with 
	| O => O 
	| S y => S (min x y) 
	end)
end.

Compute min (S O) (S (S O)).

Fixpoint max(a b : N): N :=
match a with
| O => b
| S x => (
	match b with
	| O => O
	| S y => S (max x y)
	end
)
end.

(*a-b*)
Fixpoint sub(a b : N): N :=
match b with
| O => a
| S y => match a with O => O | S x => sub x y end
end.


Fixpoint equals(a b: N): bool :=
match a with
| O => match b with | O => true | _ => false end
| S x => match b with S y => equals x y | _ => false end
end.

Compute equals (S O) (S O).

