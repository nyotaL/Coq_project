Require Import List.
Require Import Nat.
Require Import PeanoNat.
Require Import Lia.

(* In this work I implement a binary sort tree and 
   prove theorems related to it *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* First of all, I define a type Tree *)

Inductive tree : Type :=
| emp : tree
| Node : tree -> nat -> tree -> tree.

Definition empty_tree : tree := emp.

Notation "$ x" := (Node emp x emp)
                     (at level 60).

(* Function that inserts a key into the tree *)

Fixpoint insert (n : nat) (t : tree) : tree :=
  match t with
  | emp => $ n
  | Node l val r =>
          match val ?= n with
          | Eq => t
          | Lt => Node l val (insert n r)
          | Gt => Node (insert n l) val r
        end
  end.


(* Insert function doesn't return an empty tree *)

Lemma Insert_not_emp : forall (n : nat) (t : tree),
  insert n t <> empty_tree.
Proof.
  intros n t. unfold not. destruct t.
  - simpl. discriminate.
  - simpl. destruct (n0 ?= n) eqn:T.
    + discriminate.
    + discriminate.
    + discriminate.
Qed.

(* Converting tree into list *)

Fixpoint toList (t : tree) : list nat := 
  match t with
  | emp => nil 
  | Node l val r => toList(l) ++ [val] ++ toList(r)
  end.

(* Unit test for insert (and for toList) *)

Example test_insert:  toList (insert 7 ($ 5))  = [5;7].
Proof. reflexivity. Qed.

(* Now the goal is to define a binary search tree. For that,
   I inductively define a proposition which means 
   ( smth (P) holds at every Node of the tree ) *)

Fixpoint Holds (P: nat -> Prop) (t: tree) : Prop :=
  match t with
  | emp => True
  | Node l val r => P val /\ Holds P l /\ Holds P r
  end.

Inductive bst : tree -> Prop :=
| bst_emp : bst emp
| bst_Node : forall l val r, Holds (fun y => y < val) l ->
                             Holds (fun y => y > val) r ->
                             bst l -> bst r -> bst (Node l val r).

(* Unit test for bst *)

Example bst_ex1 : bst (Node ($ 4) 5 ($ 6)).
Proof.
  repeat (constructor).
Qed.

(* Empty tree is a binary sort tree *)

Theorem emp_is_bst : bst empty_tree.
Proof.
  apply bst_emp.
Qed. 

(* Now the goal is to prove a very important fact:
   Inserting an element into bst returns bst *)

(* To prove that, I state a helper lemma which says
   that if predicate P holds on the bst and on the key, it also 
   holds on a tree returned by the insert function *) 

Lemma Holds_insert: forall (P : nat -> Prop) (t : tree),
  Holds P t -> forall (n : nat), P n -> Holds P (insert n t).
Proof.
  intros P. induction t.
  - simpl. intros T n HPn. split.
    + apply HPn.
    + split. apply T. apply T.
  - intros [HPn [H1 H2]].
    intros n0. intros HPn0. simpl. destruct (n ?= n0) eqn:T.
    + simpl. split.
      * apply HPn.
      * split. apply H1. apply H2.
    + simpl. split.
      * apply HPn.
      * split.
        ** apply H1.
        ** apply IHt2. apply H2. apply HPn0.
    + simpl. split.
      * apply HPn.
      * split.
        ** apply IHt1. apply H1. apply HPn0.
        ** apply H2.
Qed.

(* And the theorem itself *)

Theorem insert_bst : forall (n : nat) (t : tree),
  bst t -> bst (insert n t).
Proof.
  intros n t E. induction E.
  - simpl. apply bst_Node.
    + simpl. apply I.
    + simpl. apply I.
    + apply bst_emp.
    + apply bst_emp.
  - simpl. destruct (val ?= n) eqn:T.
    + apply bst_Node.
      * apply H.
      * apply H0.
      * apply E1.
      * apply E2.
    + apply bst_Node.
      * apply H.
      * apply Holds_insert.
        ** apply H0.
        ** rewrite Nat.compare_lt_iff in T. apply T.
      * apply E1.
      * apply IHE2.
    + apply bst_Node.
      * apply Holds_insert.
        ** apply H.
        ** rewrite Nat.compare_gt_iff in T. apply T.
      * apply H0.
      * apply IHE1.
      * apply E2.
Qed.


(* Next I define a function for finding an element
   in the tree. It returns true if succeeds 
   and false otherwise *) 

Fixpoint find (n : nat) (t : tree) : bool :=
  match t with 
  | emp => false
  | Node l val r => 
            match n ?= val with
            | Eq => true
            | Lt => find n l
            | Gt => find n r
            end
  end.

(* Simple unit tests for find function *)

Example test_find: find 3 (Node (Node ($ 3) 4 emp) 5 ($ 6)) = true.
Proof. reflexivity. Qed.

Example test_find2: find 10 (Node (Node ($ 3) 4 emp) 5 ($ 6)) = false.
Proof. reflexivity. Qed.

(* Here I prove a fact that after insertion an element
   is in the tree *)

Theorem find_insert: forall (n : nat) (t : tree),
  find n (insert n t) = true.
Proof.
  intros n. induction t.
  - simpl. rewrite Nat.compare_refl. reflexivity.
  - destruct (n0 ?= n) eqn:T.
    + simpl. rewrite T. apply Nat.compare_eq in T.
      rewrite T. simpl. rewrite Nat.compare_refl. 
      reflexivity.
    + simpl. rewrite T. simpl. 
      rewrite Nat.compare_antisym in T. 
      apply CompOpp_iff in T. simpl in T.
      rewrite T. apply IHt2.
    + simpl. rewrite T. simpl.
      rewrite Nat.compare_antisym in T.
      apply CompOpp_iff in T. simpl in T.
      rewrite T. apply IHt1.
Qed.

Fixpoint size (t : tree) : nat :=
  match t with
  | emp => 0
  | Node l val r => S (size l + (size r))
  end.

(* If an element is inserted into the tree wasn't 
   there before, tree size increments *)

Theorem insert_size : forall (n : nat) (t : tree),
  find n t = false -> size (insert n t) = S (size t).
Proof.
  intros n t. induction t.
  - simpl. reflexivity.
  - simpl. destruct (n0 ?= n) eqn:T.
    + simpl. rewrite Nat.compare_antisym in T.
      apply CompOpp_iff in T. simpl in T.
      rewrite T. intros contra. discriminate contra.
    + rewrite Nat.compare_antisym in T.
      apply CompOpp_iff in T. simpl in T.
      rewrite T. simpl. intros FH. apply IHt2 in FH.
      rewrite FH. apply eq_S.
      rewrite Nat.add_comm. apply eq_S.
      rewrite Nat.add_comm. reflexivity.
    + rewrite Nat.compare_antisym in T.
      apply CompOpp_iff in T. simpl in T.
      rewrite T. simpl. intros FH. apply IHt1 in FH.
      rewrite FH. apply eq_S. simpl.
      apply eq_S. reflexivity.
  Qed.

(* Now, I proceed to the remove function *)

(* First of all, I define a min_elem function,
   which returns the smalest key value in bst.
   This function will be used only in case of Node 
   constructor, so let it return zero when bst is empty *)

Fixpoint min_elem (t : tree) : nat :=
  match t with
  | emp => 0
  | Node emp val r => val
  | Node l val r => min_elem l
  end.

(* The remove element function follows *)

Fixpoint remove (n : nat) (t : tree) : tree :=
  match t with
  | emp => emp
  | Node l val r =>
          match val ?= n with
          | Lt => Node l val (remove n r)
          | Gt => Node (remove n l) val r
          | Eq => 
               match l, r with
               | emp , _ => r
               | _ , emp => l
               | _ , Node l_r val_r r_r => Node l (min_elem r) (remove (min_elem r) r)
              end
        end
  end.

(* Here are some unit test for the defined functions *)

Example test_min_elem: min_elem (Node (Node ($ 3) 4 emp) 5 ($ 6)) = 3.
Proof. reflexivity. Qed.

Example test_remove: toList (remove 4 (Node (Node ($ 3) 4 emp) 5 ($ 6))) = [3;5;6].
Proof. reflexivity. Qed.

(* The next theorem to be proved is that removing an element from bst
   keeps the bst invariant *)

Lemma min_shift : forall (l' r' r : tree) (v' v : nat),
  min_elem (Node (Node l' v' r') v r) = min_elem (Node l' v' r').
Proof.
  intros l' r' r v' v.
  reflexivity.
Qed.

Lemma Holds_min: forall (P : nat -> Prop) (l r : tree) (n : nat),
  Holds P (Node l n r) -> P (min_elem (Node l n r)).
Proof.
  intros P. induction l. 
  - intros r. intros n. simpl. intros [HPn [HPl HPr]]. apply HPn.
  - intros r. intros n0. intros [HPn [H1 H2]]. rewrite -> min_shift.
    apply IHl1. apply H1.
Qed. 

Lemma Holds_remove: forall (P : nat -> Prop) (t : tree),
  Holds P t -> forall (n : nat), Holds P (remove n t).
Proof.
  intros P. induction t.
  - simpl. intros T N. apply I.
  - intros [H1 [H2 H3]]. intros n0. destruct (n ?= n0) eqn:T.
    + simpl. rewrite T. destruct t1 eqn:T1.
      * apply H3.
      * destruct t2 eqn:T2.
        ** apply H2.
        ** split. 
          *** apply Holds_min. apply H3.
          *** split. apply H2. apply IHt2. apply H3.
    + simpl. rewrite T. split.
      * apply H1.
      * split.
        ** apply H2.
        ** apply IHt2. apply H3.
    + simpl. rewrite T. split.
      * apply H1.
      * split.
        ** apply IHt1. apply H2.
        ** apply H3.
Qed.

Lemma Holds_lt_min : forall (n val : nat) (t : tree),
 n > val /\ Holds (fun y : nat => y < val) t -> Holds (fun y : nat => y < n) t.
Proof.
  intros n val t. intros [H1 H2]. induction t.
  - simpl. apply I.
  - simpl. destruct H2 as [H3 [H4 H5]]. split.
    ++ apply Gt.gt_trans with val. apply H1. apply H3.
    ++ split.
      * apply IHt1. apply H4.
      * apply IHt2. apply H5.
Qed. 

Lemma Holds_gt_min : forall (n val : nat) (t : tree),
 n < val /\ Holds (fun y : nat => y > val) t -> Holds (fun y : nat => y > n) t.
Proof.
  intros n val t. intros [H1 H2]. induction t.
  - simpl. apply I.
  - simpl. destruct H2 as [H3 [H4 H5]]. split.
    ++ apply Nat.lt_trans with val. apply H1. apply H3.
    ++ split.
      * apply IHt1. apply H4.
      * apply IHt2. apply H5.
Qed. 

Lemma Holds_gte_min : forall (n val : nat) (t : tree),
 n <= val /\ Holds (fun y : nat => y >= val) t -> Holds (fun y : nat => y >= n) t.
Proof.
  intros n val t. intros [H1 H2]. induction t.
  - simpl. apply I.
  - simpl. destruct H2 as [H3 [H4 H5]]. split.
    ++ apply Nat.le_trans with val. apply H1. apply H3.
    ++ split.
      * apply IHt1. apply H4.
      * apply IHt2. apply H5.
Qed. 

Lemma Holds_eq : forall (n : nat) (r : tree),
  Holds (fun y : nat => y > n) r -> Holds (fun y : nat => y >= n) r.
Proof.
  intros n. induction r.
  - simpl. intros T. apply T.
  - simpl. intros [H [H1 H2]]. split.
    + assert (T: S n0 > n). 
      { apply Gt.gt_trans with n0. apply Gt.gt_Sn_n. apply H. }
      apply Gt.gt_S_le. apply T.
    + split. 
      ++ apply IHr1. apply H1.
      ++ apply IHr2. apply H2.
Qed.

Lemma root_min : forall (l r : tree) (n : nat),
  bst (Node l n r) -> n >= min_elem (Node l n r).
Proof.
  induction l. 
  - intros r n BST. simpl. apply Nat.le_refl. 
  - intros r n0 BST. rewrite min_shift. inversion BST.
    inversion H2. assert (Q: n >= min_elem (Node l1 n l2)). 
    { apply IHl1. apply H4. } assert (Q1: n0 >= n). 
    { apply Gt.gt_le_S in H6. apply Nat.le_trans with (S n). apply Nat.le_succ_diag_r. apply H6. }
    apply Nat.le_trans with n. apply IHl1. apply H4. apply Q1.
Qed.

Lemma Min_is_min : forall (l r : tree) (n : nat),
  bst (Node l n r) -> 
       Holds (fun y : nat => y >= min_elem (Node l n r)) (Node l n r). 
Proof.
  induction l.
  - intros r n BST. simpl. split. apply Nat.le_refl. split. apply I.
    inversion BST. apply Holds_eq. apply H3.
  - intros r n0 BST. split.
    + apply root_min. apply BST.
    + split. rewrite min_shift. apply IHl1. inversion BST. apply H4.
      inversion BST. apply Holds_gte_min with n0. split.
      apply root_min. apply BST. apply Holds_eq. apply H3.
Qed.


Lemma Holds_geq_remove_ge t x : bst t -> Holds (fun y => y >= x) t ->
        Holds (fun y => y > x) (remove x t).
Proof with auto. induction t; intros BST H...
simpl. destruct (n ?= x) eqn:E.
- apply Nat.compare_eq in E. destruct t1.
  + destruct H as [_ [_ H]]. inversion BST. subst. apply H4.
  + destruct t2. destruct H as [_ [H _]]. inversion BST. subst.
    * inversion H. inversion H3. lia. (* there're two inconsistent inequalities *)
    * split.
      apply Holds_min. inversion BST. subst. apply H4.
      (* H and BST are inconsistent *)
      inversion BST. inversion H. subst.
      inversion H3. destruct H8 as [H8 _]. inversion H8. lia.
- simpl. apply Nat.compare_lt_iff in E. inversion BST. inversion H. subst. lia.
- apply Nat.compare_gt_iff in E. simpl. inversion BST. inversion H. subst. split.
  + apply E.
  + split. apply IHt1. apply H5. destruct H8 as [H1 _]. apply H1. apply Holds_gt_min with n.
    split. apply E. apply H4.
Qed. 

Lemma min_Nod : forall (n val : nat) (l r : tree),
   Holds (fun y: nat => y > val) l /\ n > val -> min_elem (Node l n r) > val.
Proof.
  intros n val l. destruct l.
  - intros r. intros [H U]. simpl. apply U.
  - intros r. intros [T Q]. rewrite min_shift. apply Holds_min in T. apply T.
Qed.


Theorem remove_bst : forall (t : tree) (n : nat),
  bst t -> bst (remove n t).
Proof.
  induction t. intros n E.
  - simpl. apply bst_emp.
  - intros n0 E. simpl. destruct (n ?= n0) eqn:T.
    + destruct t1 eqn:Tl.
      * inversion E. apply H5.
      * destruct t2 eqn:Tr.
        ** inversion E. apply H4.
        ** apply bst_Node.
          *** split. 
             ++ inversion E. inversion H2. inversion H3. apply min_Nod. 
                split. apply Holds_gt_min with n. split. apply H6. 
                destruct H9 as [Q _]. apply Q. apply Gt.gt_trans with n. 
                apply H8. apply H6.
             ++ split. inversion E. inversion H2. apply Holds_lt_min with n.
                split. apply min_Nod. inversion H3. destruct H9 as [Q _].
                split. apply Q. apply H8. destruct H7 as [Q _]. apply Q. 
                apply Holds_lt_min with n. split. apply min_Nod. inversion E.
                inversion H3. destruct H3 as [Q _]. destruct H7 as [K _].
                split. apply K. apply Q. inversion E. inversion H2.
                destruct H2 as [_ Q]. apply Q.
          *** apply Holds_geq_remove_ge. inversion E. apply H5. apply Min_is_min.
              inversion E. apply H5.  
          *** inversion E. apply H4.
          *** apply IHt2. inversion E. apply H5. 
    + apply bst_Node.
      * inversion E. apply H2.
      * apply Holds_remove. inversion E. apply H3.
      * inversion E. apply H4.
      * apply IHt2. inversion E. apply H5.
    + apply bst_Node.
      * apply Holds_remove. inversion E. apply H2.
      * inversion E. apply H3.
      * apply IHt1. inversion E. apply H4.
      * inversion E. apply H5.
Qed.














