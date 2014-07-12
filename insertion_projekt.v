Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import BauerSorting.
Open Scope Z_scope.


(** 
   Pomozna funckija za vstavljanje celega stevila x v seznam celih stevil l.
**)
Fixpoint insert (x: Z) (l: list Z): list Z :=
   match l with
      | nil => x :: nil   (* Robni primer - stakni glavo (x) z praznim seznamom, x je torej trenutno najmanjsi element, ki smo ga obdelali *)
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

Hint Resolve urejen_head urejen_tail : urejenost.

Lemma manjse_enako (a: Z) (b: Z): a < b -> a <= b.
Proof.
  intro.
  case (Z_le_gt_dec a b).
  - intro.
    assumption.
  - intro.
    firstorder.
Qed.


Hint Resolve urejen_tail urejen_head urejen_lt_cons : urejen_hint.
Lemma ohranjanje_urejenosti_vstavljanja (x: Z) (l: list Z): urejen l -> urejen(insert x l).
Proof.
   intro.
   induction l.
   - auto. (* Vstavljanje v prazen seznam *)
   - simpl. (* Netrivialen primer *)
     case (Z_le_gt_dec x a). (* Primerjamo element, ki ga vstavljamo, s trenutno glavo *)
     * simpl. 
       auto.
     * intro.
       simpl.
       destruct l.
       + simpl.
         split.
         Focus.
           apply manjse_enako.
           firstorder.
           assumption. (* Vedno predpostavimo resnico *)
       + simpl.
         case (Z_le_gt_dec x z).
         Focus.
           split.
           Focus.
           firstorder.
           simpl.
           split.
           Focus.
             assumption.
             firstorder.
             intro.
             split.
             Focus.
                firstorder.
                simpl.
                firstorder.
                apply urejen_tail in H0.
                elim H.
                elim g0.
                admit.
Qed.

(* Rezulat insterition sorta je urejen seznam... *)
Theorem insertion_sort_deluje_1: forall lst: list Z, urejen (insertion_sort lst).
Proof.
   intro.
   (*unfold urejen.*)
   induction lst.
   - reflexivity. (* Trivialen primer *)
   - apply ohranjanje_urejenosti_vstavljanja. (* Tu uporabi pomozno lemo *)
     auto.
     (*unfold insert.*)
Qed.

(* ... ki je obenem permutacija vhodnega seznama *)
Theorem insertion_sort_deluje_2: forall lst: list Z, permutiran lst (insertion_sort lst).
Proof.
   induction lst.
   - unfold insertion_sort.
     apply permutiran_refl. (* to je v BauerSortu *)
   - destruct lst.
     + apply permutiran_refl. (* to je v BauerSortu *)
     + case_eq (a =? z). (* tu uporabi pomozno lemo *)
       * intro.
         simpl.
         admit.
       * admit.
Qed.
  
Lemma ohranjanje_vsebovanosti_seznama