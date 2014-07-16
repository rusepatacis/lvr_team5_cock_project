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

(* Pomozna lema, uporabljena v dokazu ohranjanje_urejenosti_vstaljanja *)
Lemma manjse_enako (a: Z) (b: Z): a < b -> a <= b.
Proof.
  intro.
  case (Z_le_gt_dec a b).
  - intro.
    assumption.
  - intro.
    firstorder.
Qed.

Hint Resolve urejen_tail urejen_head urejen_lt_cons najmanjsi_inv najmanjsi_In najmanjsi_head najmanjsi_tail : urejen_hint.

Lemma ohranjanje_urejenosti_vstavljanja (x: Z) (l: list Z): urejen l -> urejen(insert x l).
Proof.
   intro. (* Vpeljava *)
   induction l. (* Dokaz z indukcijo po senznamu l *)
   - auto. (* Vstavljanje v prazen seznam *)
   - simpl. (* Netrivialen primer *)
     case (Z_le_gt_dec x a). (* Primerjamo element, ki ga vstavljamo, s trenutno glavo *)
     * simpl. (* Primer x <= a: samo staknemo x na zacetku, seznam je urejen *)
       auto.
     * intro. (* Primer x > a: potujemo po seznamu in x vstavimo na ustrezno mesto. *)
       simpl.
       destruct l. (* Locimo primere glede na seznam *)
       + simpl. (* Prazen seznam *)
         split.
            apply manjse_enako.
            firstorder.

            assumption. (* Vedno predpostavimo resnico *)
       + simpl. (* Seznam sestavljen iz glave in repa *)
         case (Z_le_gt_dec x z). (* Locimo primere glede na primerjavo z glavo *)
           simpl. (* x <= z ; razpise definicijo urejen*)
           intros. (* Dokazujemo implikacijo *)
           split. (* Dokaz konjunkcije *)
             firstorder. (* Telovadba z neenakostmi *)
             
             split. (* Dokaz konjunkcije *)
              assumption.
              firstorder.
           
           split. (* x > z *)
              firstorder. (* Telovadba z neenakostmi *)
           
              replace (z :: insert x l) with (insert x (z :: l)). (* Ker zelimo uporabiti hipotezo IHl (njen desni del *)
              apply urejen_tail in H. (* Poenostavimo H, da ustreza levemu delu IHl in s tem pridobimo 'desni del' IHl *)
              firstorder.  (* Ocitno iz implikacije v hipotezah *)
              simpl. (* Razpis insert *)
              firstorder. (* Poenostavimo kar se da v hipotezah *)
              destruct (Z_le_gt_dec x z). (* V hipotezah imamo ustrezen pogoj, moti nas notacija Z_le_gt_dec, zelimo > <= *)
              firstorder.
              firstorder.
Qed.

(* ::: Dokaz pravilnosti ::: *)

(* Rezulat insterition sorta je urejen seznam... *)
Theorem insertion_sort_deluje_1: forall lst: list Z, urejen (insertion_sort lst).
Proof.
   intro.
   (*unfold urejen.*)
   induction lst.
   - reflexivity. (* Trivialen primer *)
   - apply ohranjanje_urejenosti_vstavljanja. (* Tu uporabi pomozno lemo *)
     auto.
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
  
