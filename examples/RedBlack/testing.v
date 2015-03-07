Require Import QuickChick.
Require Import GenLow GenHigh.
Import GenLow GenHigh.
Require Import NPeano.

Require Import ssreflect ssrnat ssrbool eqtype.

Require Import redblack.

Require Import List String.
Import ListNotations.

Open Scope string.

Open Scope Checker_scope.

(* Red-Black Tree invariant: executable definition *)

Fixpoint black_height_bool (t: tree) : option nat :=
  match t with
    | Leaf => Some 0
    | Node c tl _ tr =>
      let h1 := black_height_bool tl in
      let h2 := black_height_bool tr in
      match h1, h2 with
        | Some n1, Some n2 =>
          if n1 == n2 then
            match c with
              | Black => Some (S n1)
              | Red => Some n1
            end
          else None
        | _, _ => None
      end
  end.

Definition is_black_balanced (t : tree) : bool :=
  isSome (black_height_bool t).

Fixpoint has_no_red_red (c : color) (t : tree) : bool :=
  match t with
    | Leaf => true
    | Node Red t1 _ t2 => 
      match c with 
        | Red => false 
        | Black => has_no_red_red Red t1 && has_no_red_red Red t2
      end
    | Node Black t1 _ t2 => 
      has_no_red_red Black t1 && has_no_red_red Black t2
  end.

(* begin is_redblack_bool *)
Definition is_redblack_bool (t : tree) : bool := 
  is_black_balanced t && has_no_red_red Red t.
(* end is_redblack_bool *)

Fixpoint showColor (c : color) :=
  match c with
    | Red => "Red"
    | Black => "Black"
  end.

Fixpoint tree_to_string (t : tree) :=
  match t with
    | Leaf => "Leaf"
    | Node c l x r => "Node " ++ showColor c ++ " "
                            ++ "(" ++ tree_to_string l ++ ") "
                            ++ show x ++ " "
                            ++ "(" ++ tree_to_string r ++ ")"
  end.

Instance showTree {A : Type} `{_ : Show A} : Show tree :=
  {|
    show t := "" (* CH: tree_to_string t causes a 9x increase in runtime *)
  |}.

(* begin insert_preserves_redblack_checker *)
Definition insert_is_redblack_checker (genTree : G tree) : Checker :=
  forAll arbitrary (fun n => forAll genTree (fun t =>
    is_redblack_bool t ==> is_redblack_bool (insert n t))).
(* end insert_preserves_redblack_checker *)


Module DefaultNotation.

Notation " 'elems' [ x ] " := (elements x (cons x nil)) : qc_scope.
Notation " 'elems' [ x ; y ] " := (elements x (cons x (cons y nil))) : qc_scope.
Notation " 'elems' [ x ; y ; .. ; z ] " :=
  (elements x (cons x (cons y .. (cons z nil) ..))) : qc_scope.

Notation " 'choose' [ x ] " := (oneof x (cons x nil)) : qc_scope.
Notation " 'choose' [ x ; y ] " := (oneof x (cons x (cons y nil))) : qc_scope.
Notation " 'choose' [ x ; y ; .. ; z ] " :=
  (oneof x (cons x (cons y .. (cons z nil) ..))) : qc_scope.

End DefaultNotation.
Import DefaultNotation. Open Scope qc_scope.

(* begin genAnyTree *)
Definition genColor := elems [Red; Black].
Fixpoint genAnyTree_height (h : nat) : G tree :=
  match h with 0    => returnGen Leaf
             | S h' => liftGen4 Node genColor (genAnyTree_height h')
                                    arbitrary (genAnyTree_height h') end.
Definition genAnyTree : G tree := sized genAnyTree_height.
(* end genAnyTree *)

Extract Constant defSize => "5".
Extract Constant Test.defNumTests => "10".
(* begin QC_naive *)
QuickCheck (insert_is_redblack_checker genAnyTree).
(* end QC_naive *)
Extract Constant Test.defNumTests => "10000".

Module DoNotation.
Import ssrfun.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.
Import DoNotation.

Require Import Relations.

Definition wf_hc (hc1:nat*color) (hc2:nat*color) : Prop :=
  fst hc1 < fst hc2 \/ (fst hc1 = fst hc2 /\
  match snd hc1, snd hc2 with
  | Red, Black => True
  | _, _ => False
  end).

Lemma well_founded_hc : well_founded wf_hc.
Admitted.

Require Import Program.Wf.

(* begin genRBTree_height *)
Program Fixpoint genRBTree_height (hc : nat*color) {wf wf_hc hc} : G tree :=
  match hc with
    | (0, Red) => returnGen Leaf
    | (0, Black) => choose [returnGen Leaf;
                      (do! n <- arbitrary; returnGen (Node Red Leaf n Leaf))]
    | (S h, Red) => liftGen4 Node (returnGen Black) (genRBTree_height (h, Black))
                                          arbitrary (genRBTree_height (h, Black))
    | (S h, Black) => do! c' <- genColor;
                      let h' := match c' with Red => S h | Black => h end in
                      liftGen4 Node (returnGen c') (genRBTree_height (h', c'))
                                         arbitrary (genRBTree_height (h', c')) end.
(* end genRBTree_height *)
Next Obligation. unfold wf_hc. simpl. left; apply/ltP; omega. Qed.
Next Obligation. unfold wf_hc. simpl. left; apply/ltP; omega. Qed.
Next Obligation. unfold wf_hc. simpl.
                 destruct c'. right. tauto. left; apply/ltP; omega. Qed.
Next Obligation. unfold wf_hc. simpl.
                 destruct c'. right. tauto. left; apply/ltP; omega. Qed.
Next Obligation. apply well_founded_hc. Defined.


(* begin genRBTree *)
Definition genRBTree := sized (fun h => genRBTree_height (h, Red)).
(* end genRBTree *)

Definition showDiscards (r : Result) :=
  match r with
  | Success ns nd _ _ => "Success: number of successes " ++ show (ns-1) ++ newline ++
                         "         number of discards "  ++ show nd ++ newline
  | _ => show r
  end.

Definition testInsert :=
  showDiscards (quickCheck (insert_is_redblack_checker genRBTree)).

Extract Constant defSize => "10".
Extract Constant Test.defNumTests => "10000".
(* begin QC_good *)
QuickCheck (insert_is_redblack_checker genRBTree).
(* end QC_good *)
