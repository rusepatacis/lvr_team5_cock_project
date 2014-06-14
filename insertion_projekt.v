Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import BauerSorting.

Print urejen.

(** 
   Pomozna funckija za vstavljanje celega stevila x v seznam celih stevil l.
**)
Fixpoint insert (x: Z) (l: list Z): list Z :=
   match l with
      | nil => x :: l   (* Robni primer - stakni glavo (x) z praznim seznamom, x je torej trenutno najmanjsi element, ki smo ga obdelali *)
      | (cons y l') =>  (* Seznam, staknjen iz glave y in repa l' *)
           if (Z_le_gt_dec x y) then 
              (** Element x je manjsi ali enak od trenutne glave y, vstavi x * *)
              (x :: l)
           else 
              (** Element x je vecji od trenutne glave y,
               poklici rekurzijo, potuj po seznamu, dokler ne prides do manjsega elementa **)
              (y :: (insert x l'))      
      end.

(** 
   Glavna funkcija insertion_sort  za cela stevila
**)
Fixpoint insertion_sort (l: list Z): list Z :=
   match l with
      | nil => nil (* Prazen seznam je urejen *)
      | (cons x l') => insert x (insertion_sort l') (* Potuj po seznamu, premikaj trenutno glavo na ustrezno mesto *)
   end.


(* Primer sortiranja *)
Eval compute in (insertion_sort (2::6::1::3::9::7::0::nil)%Z).

(* Rezulat insterition sorta je urejen seznam... *)
Theorem insertion_sort_deluje_1: forall lst: list Z, urejen (insertion_sort lst).
Proof.
   intro.
   unfold urejen.
   induction lst.
   - admit.
   - admit.
Qed.

(* ... ki je obenem permutacija vhodnega seznama *)
Theorem insertion_sort_deluje_2: forall lst: list Z, permutiran lst (insertion_sort lst).
Proof.
   admit.
Qed.
  