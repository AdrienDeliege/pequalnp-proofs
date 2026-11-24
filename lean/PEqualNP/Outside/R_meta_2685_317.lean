import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Induct on the remaining incidences, adding at most one vertex to the cover per deletion.
-- The star compiler and final wire-label translation follow the matching reduction R_meta_2685_41.
theorem PEqualNP.Outside.R_meta_2685_317
    (peel : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      E.Nonempty →
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ (F : Finset (Fin n × Fin m)) (K : Circuit), F ⊂ E ∧
        ((∃ p, ∀ e ∈ E, e ∉ F → e.1 = p) ∨ (∃ l, ∀ e ∈ E, e ∉ F → e.2 = l)) ∧
        IsAO2 (n+m) K ∧
        (∀ z, circuitFun (n+m) K z = decide (∃ p l, (p,l) ∈ F ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        (if F = ∅ then 0 else K.size + 1) + (E.card - F.card) ≤ C.size)
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : Circuit) (S : Bool → Finset ℕ),
        IsAO2 (n+m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := NestedCover.gateAt D
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n+m+i ∧ (g i).op = GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = GateOp.and →
          ∃ a b t, (g i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  intro n m I _ C square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have build (T : Finset (Fin n × Fin m)) :
      ∀ (K : Circuit), (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p,l) ∈ T ∧ (p,s) ∈ T ∧ (q,l) ∈ T ∧ (q,s) ∈ T)) →
      IsAO2 (n+m) K →
      (∀ z, circuitFun (n+m) K z = decide (∃ p l, (p,l) ∈ T ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ T, e.1 ∈ A ∨ e.2 ∈ B) ∧
        T.card + A.card + B.card ≤ (if T = ∅ then 0 else K.size + 1) := by
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro K sq valid val
      by_cases empty : T = ∅
      · subst T
        exact ⟨∅,∅,by simp,by simp⟩
      obtain ⟨F,J,sub,star,jok,jval,saving⟩ := peel n m T K
        (Finset.nonempty_iff_ne_empty.mpr empty) sq valid val
      have small : F.card ≤ T.card := Finset.card_le_card sub.le
      have sqF : ∀ p q l s, p ≠ q → l ≠ s →
          ¬ ((p,l) ∈ F ∧ (p,s) ∈ F ∧ (q,l) ∈ F ∧ (q,s) ∈ F) := by
        intro p q l s hp hl h
        exact sq p q l s hp hl ⟨sub.le h.1,sub.le h.2.1,sub.le h.2.2.1,sub.le h.2.2.2⟩
      obtain ⟨A,B,cov,budget⟩ := ih F sub J sqF jok jval
      rw [if_neg empty]
      rcases star with ⟨p,hp⟩ | ⟨l,hl⟩
      · refine ⟨insert p A,B,?_,?_⟩
        · intro e he
          by_cases hf : e ∈ F
          · exact (cov e hf).imp (Finset.mem_insert_of_mem) id
          · exact Or.inl (Finset.mem_insert.mpr (Or.inl (hp e he hf)))
        · have := Finset.card_insert_le p A
          omega
      · refine ⟨A,insert l B,?_,?_⟩
        · intro e he
          by_cases hf : e ∈ F
          · exact (cov e hf).imp id (Finset.mem_insert_of_mem)
          · exact Or.inr (Finset.mem_insert.mpr (Or.inl (hl e he hf)))
        · have := Finset.card_insert_le l B
          omega
  obtain ⟨A,B,cover,cost⟩ := build E C (by simpa only [mem] using square) ao
    (by simpa only [mem] using correct)
  have budget : E.card + A.card + B.card ≤ C.size + 1 :=
    cost.trans (by split <;> omega)
  obtain ⟨D,S,strict,size,eval,closed,ands⟩ := stars n m E A B cover
  refine ⟨D,S false,S true,strict,by simpa only [mem] using eval,by omega,?_,?_,?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_,side⟩ | gate
    · exact Or.inl (by simpa using side)
    · exact Or.inr gate
  · intro w hw
    rcases closed true w hw with ⟨bound,side⟩ | gate
    · exact Or.inl ⟨by simpa using side,bound⟩
    · exact Or.inr gate
  · intro i hi hand
    obtain ⟨a,b,t,inputs,ha,hb⟩ := ands i hi hand
    refine ⟨a,b,inputs,?_⟩
    cases t with
    | false => exact Or.inl ⟨ha,hb⟩
    | true => exact Or.inr ⟨ha,hb⟩
