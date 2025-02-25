Require Import Arith.
Require Import List.
Import ListNotations.



(*
	goal: define states and transitions
	state: object in a set, called statelist
	transition: relation from state to state

	TLA+ uses states and transitions
	transition written in terms of primed and unprimed variables
	variables have specific values in states
	safety property: model never goes into a specific state
	liveness property: stuttering notwithstanding, desirable states are reached

	simple example:
	model with two states A and B
	transiton from A to B
	prove the following:
	starting at A, model can reach B
	starting at B, model cannot reach A

	formally:
	S = {A,B}
	T = {(A,B)}
	R: S -> S
	V in R(S) if U in S and (U,V) in T
	final set of reachable states is a fixed point of R
	if T is finite, such a fixed point should exist

	core problem:
	rewrite safety and liveness properties of courier
	build a model similar to courier
	not a perfect 1-1 translation from TLA+, design notes are used to base things off of.

	Coq is based off type-checking at its core, uses CIC.

	two types of objects in Coq:
	Type sort and Prop sort
	Prop is well-formed proposition
	Type is for mathematical structures

*)

Check true.
Check false.

Inductive state : Type :=
| init
| unsafe
| safe.

Definition is_safe(s:state) : bool :=
match s with
| unsafe => false
| _ => true
end.

Compute is_safe init.

Example init_is_safe:
	is_safe init = true.
Proof.
simpl.
reflexivity.
Qed.

Inductive states_simple : Type := 
| A
| B.

Definition is_transition_bool(x y: states_simple): bool :=
match x with
| A => match y with B => true | _ => false end
| _ => false
end.

Compute is_transition_bool B A.
Compute is_transition_bool A B.

Definition AND (u v: bool) :=
match u, v with
| true, true => true
| _ , _ => false
end.

(* Definition for functions, Fixpoint for recursive functions

Better to treat as propositions, but this restricts us to Calculus of Constructions
*)

Definition is_transition(x y: states_simple): Prop :=
match x with
| A => match y with
	| B => True
	| _ => False
	end
| _ => False
end.

Compute is_transition A A.


(*
Fixpoint is_reachable(x y: states_simple): Prop :=
is_transition_prop x y \/ (exists w : states_simple, is_transition_prop x w /\ is_reachable w y).

this fails since there is no decreasing argument for is_reachable
computing it can take an infinitely long amount of time
one solution is a breadth-first search approach, but this relies on staes being in a poset
*)

(*
	can unreachability be proven without an explicit computation of reachability?
	A is the initial state
	B is the final state
*)

(*
	if B is unreachable, it is equivalent to saying that all states that can reach B are themselves unreachable

	In a simple case such as this, it is obvious to the reader that no way exists to reach B, and that the model is finite
	However, computing reachability is not possible
	proving a particular state is reachable is simple
*)

Theorem first_theorem :
	is_transition A B.
Proof.
simpl.
reflexivity.

(*
	probelm - system so far relies on explictly enumerated states
	no notion of variables yet
	transition system needs to be written explicitly

	proving unreachability in CoC is a problem:
	- quantifying it requires some use of law of excluded middle

	defining reachability with an obvious decreasing quantity:

	R(a,b,S) is defined as - a can lead to b via elements in S

	R(a, b, S) = T(a,b) \/ exists c in S-{a,b}: T(a,c) /\ R(c,S-{a,b})
	here |S| is a decreasing quantity 

	set membership is a proposition?

	II subset for live super for safety
	define good and bad explicitly as sets and avoid negation using II
	how to phrase safety vs liveness
	set of transitions is finite

*)



