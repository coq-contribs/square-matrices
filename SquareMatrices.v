(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(*
  This development is a formalization of Chris Okasaki's article
  ``From Fast Exponentiation to Square Matrices: An Adventure in Types''
*)

Set Implicit Arguments.

Require Export Arith.
Open Scope nat_scope.

(*** Fast exponentiation *) 

Fixpoint half (n:nat) : nat := match n with
  | O => O
  | S O => O
  | S (S p) => S (half p)
end.

Fixpoint even (n:nat) : bool := match n with
  | O => true
  | S O => false
  | S (S p) => even p
end.

Inductive half_dom : nat -> Prop :=
  | half_0 : half_dom O
  | half_2 : forall p, half_dom (half p) -> half_dom p.

Hint Constructors half_dom.

Definition half_inv : forall x p, half_dom x -> x = S p ->
  (half_dom (half (S p))).
Proof.
  intros x p h; case h.
  intro h'; discriminate h'.
  intros.
  rewrite <- H0; assumption.
Defined.
Print half_inv.

Fixpoint fastexp
  (c:nat) (x:nat) (n:nat) (h:half_dom n) { struct h } : nat :=
  match n as y return n=y -> nat with
  | O => fun _ => c 
  | S p => fun hp => 
     if even n then 
      @fastexp c (x*x) (half (S p)) (half_inv h hp)
     else
      @fastexp (c*x) (x*x) (half (S p)) (half_inv h hp)
  end (refl_equal n).

Implicit Arguments fastexp [].

Definition exp x n (h:half_dom n) := fastexp 1 x n h.

Implicit Arguments exp [].

Definition half_dom_5 : half_dom 5. auto. Defined.

Definition half_dom_8 : half_dom 8. auto. Defined.

Eval compute in exp 2 5 half_dom_5.

Extraction fastexp.

(* all naturals are in half_dom *)

Require Export Wf_nat.

Definition half_le : forall n, half n <= n.
Proof.
  induction n using (well_founded_ind lt_wf).
  destruct n; simpl; auto.
  destruct n; simpl; auto with arith.
Defined.
Hint Resolve half_le.

Definition half_lt : forall n, 0<n -> half n < n.
Proof.
  induction n using (well_founded_ind lt_wf).
  destruct n; simpl; auto.
  destruct n; simpl; auto with arith.
Defined.
Hint Resolve half_lt.

Lemma half_dom_all : forall n, half_dom n.
Proof.
  induction n using (well_founded_ind lt_wf).
  destruct n.
  intros; exact half_0.
  apply half_2.  
  apply H; apply half_lt; auto with arith.
Defined.

Definition power x n := @exp x n (half_dom_all n).

Eval compute in power 2 5.  (* 32 *)

(* A simple property of exp *)

(***

Lemma power_S : forall x n, power x (S n) = x * power x n.

Lemma power_plus : forall x n m, power x (n+m) = power x n * power x m.
unfold power, exp.
induction n.
simpl; auto with arith.

SearchAbout plus.

***)

(*** Vectors of length n *)

Inductive vector_ (v w : Set) : Set :=
  | Vzero : v -> vector_ v w
  | Veven : vector_ v     (w*w) -> vector_ v w
  | Vodd  : vector_ (v*w) (w*w) -> vector_ v w.

Definition vector A := vector_ unit A.

Definition abcde : vector nat :=
  Vodd (Veven (Vodd (Vzero _ ((tt, 1), ((2,3), (4,5)))))).

Print abcde.

(** Creation of the vector (a,a,...,a) *)

Fixpoint vcreate_ 
  (A B:Set) (v:A) (w:B) (n:nat) (h:half_dom n) {struct h}
  : vector_ A B :=
  match n as y return n=y -> vector_ A B with
  | O => (fun _ => Vzero _ v)
  | S p => 
     (fun hp =>
     if even n then 
       Veven 
         (@vcreate_ _ _ v (w,w) (half (S p)) (half_inv h hp))
     else 
       Vodd 
         (@vcreate_ _ _ (v,w) (w,w) (half (S p)) (half_inv h hp)))
  end (refl_equal n).

Implicit Arguments vcreate_ [A B].

Definition vcreate (A:Set) (a:A) (n:nat) : vector A :=
  vcreate_ tt a n (half_dom_all n).

Implicit Arguments vcreate [A].

Eval compute in vcreate 1 5.
Eval compute in vcreate 1 8.

(** Dimension: vdim (a1,...,an) = n *)

Fixpoint vdim_ 
  (A B: Set) (nv nw: nat) (v: vector_ A B) { struct v } : nat 
:=
  match v with
  | Vzero _  => nv
  | Veven v' => vdim_ nv (nw+nw) v'
  | Vodd v'  => vdim_ (nv+nw) (nw+nw) v'
  end.

Definition vdim (A: Set) (v:vector A) : nat := vdim_ 0 1 v.

Eval compute in vdim abcde.

(** Access: vget i (a0,...,an) = ai *)

Definition getp (A B C: Set)
  (getv: nat -> A -> C) (getw: nat -> B -> C)
  (vsize: nat) (i: nat) (p: A*B) : C :=
  if le_lt_dec vsize i then 
    (* vsize <= i *) getw (i-vsize) (snd p)
  else
    (* i < vsize *) getv i (fst p).

Fixpoint vget_ 
  (A B C: Set)
  (getv: nat -> A -> option C) (vsize: nat)
  (getw: nat -> B -> option C) (wsize: nat) 
  (i: nat) (v: vector_ A B) { struct v } : option C
:=
  match v with
  | Vzero v => 
       if le_lt_dec vsize i then (*vsize<=i*) None else (*i<vsize*) getv i v 
  | Veven v' => 
     vget_ getv vsize 
       (getp getw getw wsize) (wsize+wsize) i v'
  | Vodd v' =>
     vget_ (getp getv getw vsize) (vsize+wsize)
       (getp getw getw wsize) (wsize+wsize) i v'
  end.

Definition vget (A: Set) (i: nat) (v: vector A) : option A :=
  vget_ (fun _ _ => None) 0 (fun _ b => Some b) 1 i v.

Eval compute in vget 2 abcde. 

(** Update: upd f i (a0,...,an) = (a0,...,ai-1,f ai, a+1,...,an) *)

Definition updp (A B: Set)
  (updv: nat -> A -> A) (updw: nat -> B -> B)
  (vsize: nat) (i: nat) (p: A*B) : A*B :=
  if le_lt_dec vsize i then 
    (* vsize <= i *) (fst p, updw (i-vsize) (snd p))
  else
    (* i < vsize *) (updv i (fst p), snd p).

Fixpoint vupd_ 
  (A B: Set)
  (updv: nat -> A -> A) (vsize: nat)
  (updw: nat -> B -> B) (wsize: nat) 
  (i: nat) (v: vector_ A B) { struct v } : vector_ A B
:=
  match v with
  | Vzero v0 => 
      if le_lt_dec vsize i then (*vsize<=i*) v else (*i<vsize*) Vzero _ (updv i v0)
  | Veven v' => 
     Veven 
       (vupd_ updv vsize 
         (updp updw updw wsize) (wsize+wsize) i v')
  | Vodd v' =>
     Vodd
       (vupd_ (updp updv updw vsize) (vsize+wsize)
         (updp updw updw wsize) (wsize+wsize) i v')
  end.

Definition vupd (A: Set) (f: A -> A) (i: nat) (v: vector A) : vector A :=
  vupd_ (fun _ _ => tt) 0 (fun _ b => f b) 1 i v.

Eval compute in vupd S 4 abcde.  (* (1,2,4,4,5) *)

(* correctness of vget/vupd *)
(***
Lemma vget_vupd_eq :
  forall (A:Set) (f:A->A) (i:nat) (v: vector A),
  i <= vdim v -> vget i (vupd f i v) = Some (f (vget i v)).
***)

(*** Square matrices *)

Definition Prod (v w: Set -> Set) (a: Set) := ((v a)*(w a))%type.

Inductive square_ (v w : Set -> Set) (a : Set) : Set :=
  | Mzero : v (v a) -> square_ v w a
  | Meven : square_ v (Prod w w) a -> square_ v w a
  | Modd : square_ (Prod v w) (Prod w w) a -> square_ v w a.

Definition Empty (a:Set) : Set := unit.

Definition Id (a:Set) : Set := a.

Definition square : Set -> Set := square_ Empty Id.

(* BUG: 
Definition m_3_3 :=
  Modd (Modd (Mzero _ _ nat ((tt,1), (1,1)))).
cannot define an isevar twice. Please report. *)

Definition EIII := Prod (Prod Empty Id) (Prod Id Id).
Definition IIII := Prod (Prod Id Id)    (Prod Id Id).

Definition m_3_3 : square nat :=
  Modd (Modd (Mzero EIII IIII nat 
   ((tt,
     ((tt,11),(12,13)), 
    (((tt,21),(22,23)),
     ((tt,31),(32,33))))))).

(** Dimension *)

Fixpoint mdim_ 
  (v w: Set -> Set) (a:Set)
  (nv nw: nat) (m: square_ v w a) { struct m } : nat 
:=
  match m with
  | Mzero _ => nv
  | Meven v' => mdim_ nv (nw+nw) v'
  | Modd v' => mdim_ (nv+nw) (nw+nw) v'
  end.

Definition mdim (A: Set) (m: square A) : nat := 
  mdim_ 0 1 m.

Eval compute in mdim m_3_3.

(** Creation: mcreate a n creates a square matrix of
    dimension n x n where all the elements are a. *)

Definition mkP 
  (v w : Set -> Set)
  (mkv: forall (b:Set), b -> v b)
  (mkw: forall (b:Set), b -> w b)
  : forall (b:Set), b -> Prod v w b :=
  fun (b:Set) (x:b) => (mkv b x, mkw b x).

Fixpoint mcreate_ 
  (v w : Set -> Set) 
  (mkv: forall (b:Set), b -> v b) 
  (mkw: forall (b:Set), b -> w b)
  (A:Set) (a:A) (n:nat) (h:half_dom n) {struct h}
  : square_ v w A 
:=
  match n as y return n=y -> square_ v w A with
  | O => (fun _ => Mzero _ _ _ (mkv _ (mkv _ a)))
  | S p => 
     (fun hp =>
     if even n then 
       Meven 
         (@mcreate_ _ _ mkv (mkP w w mkw mkw) 
          A a (half (S p)) (half_inv h hp))
     else 
       Modd 
         (@mcreate_ _ _ (mkP v w mkv mkw) (mkP w w mkw mkw)
          A a (half (S p)) (half_inv h hp)))
  end (refl_equal n).

Definition mcreate (A:Set) (a:A) (n:nat) (h:half_dom n) : 
  square A :=
  @mcreate_ Empty Id (fun _ _ => tt) (fun _ x => x) A a n h.

Implicit Arguments mcreate [A].

Eval compute in mcreate 1 5 half_dom_5.
Eval compute in mcreate 1 8 half_dom_8.

(** Access: mget i j m = Some m[i,j] *)

Definition getP
  (v w: Set -> Set)
  (getv: forall (b: Set), nat -> v b -> option b) 
  (getw: forall (b: Set), nat -> w b -> option b)
  (vsize: nat) 
  (b: Set) (i: nat) (p: Prod v w b) : option b :=
  if le_lt_dec vsize i then 
    (* vsize <= i *) getw _ (i-vsize) (snd p)
  else
    (* i < vsize *) getv _ i (fst p).

Fixpoint mget_ 
  (v w: Set -> Set)
  (getv: forall (b: Set), nat -> v b -> option b) (vsize: nat) 
  (getw: forall (b: Set), nat -> w b -> option b) (wsize: nat) 
  (b: Set) (i j: nat) (m: square_ v w b) { struct m } : option b
:=
  match m with
  | Mzero v => 
     match getv _ i v with 
     | None => None | Some vi => getv _ j vi end
  | Meven v' => 
     mget_ getv vsize 
       (getP getw getw wsize) (wsize+wsize) i j v'
  | Modd v' =>
     mget_ (getP getv getw vsize) (vsize+wsize)
       (getP getw getw wsize) (wsize+wsize) i j v'
  end.

Definition mget (A: Set) (i j: nat) (m: square A) : option A :=
  @mget_ Empty Id (fun _ _ _ => None) 0
                 (fun _ _ b => Some b) 1 A i j m.

Eval compute in mget 1 2 m_3_3. (* Some 23 *)

(** Update: mupd f i j m = m with m[i,j]:=f m[i,j] *)

Definition updP
  (v w: Set -> Set)
  (updv: forall (b: Set), (b->b) -> nat -> v b -> v b) 
  (updw: forall (b: Set), (b->b) -> nat -> w b -> w b)
  (vsize: nat) 
  (b: Set) (f: b->b) (i: nat) (p: Prod v w b) : Prod v w b :=
  if le_lt_dec vsize i then 
    (* vsize <= i *) (fst p, updw _ f (i-vsize) (snd p))
  else
    (* i < vsize *) (updv _ f i (fst p), snd p).

Fixpoint mupd_ 
  (v w: Set -> Set)
  (updv: forall (b: Set), (b->b) -> nat -> v b -> v b) 
  (vsize: nat) 
  (updw: forall (b: Set), (b->b) -> nat -> w b -> w b)
  (wsize: nat) 
  (b: Set) (f:b->b) (i j: nat) (m: square_ v w b) { struct m } : square_ v w b
:=
  match m with
  | Mzero v => 
     Mzero _ _ _ (updv _ (updv _ f j) i v)
  | Meven v' => 
     Meven 
       (mupd_ updv vsize 
         (updP updw updw wsize) (wsize+wsize) f i j v')
  | Modd v' =>
     Modd 
       (mupd_ (updP updv updw vsize) (vsize+wsize)
         (updP updw updw wsize) (wsize+wsize) f i j v')
  end.

Definition mupd (A: Set) (f: A -> A) (i j: nat) (m: square A) : square A :=
  @mupd_ Empty Id (fun _ _ _ _ => tt) 0
                  (fun _ f _ x => f x) 1 A f i j m.

Eval compute in mupd S 1 2 m_3_3.

(* Extractions *)

Extraction vector_.
Extraction "vector.ml" vdim vget vupd vcreate.
Extraction "matrix.ml" mdim mget mupd mcreate.
