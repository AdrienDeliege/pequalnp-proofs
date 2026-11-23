import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta707

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U (C.size) i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

end PEqualNP.Outside.LMeta707

namespace PEqualNP.Outside
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit LMeta707

theorem L_meta_707 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed →
    ∀ (D : Set (Finset (Fin n))) (S : Finset (Fin C.size)),
      (∀ i ∈ S, ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
        ∀ U ∈ D, C.gateVal U i = true ↔ ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true)) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + S.card ≤ C.size ∧
        ∀ U ∈ D, C'.eval U = C.eval U := by
  classical
  intro n C wf D S hS
  let T := Sᶜ
  let e := T.orderIsoOfFin rfl
  let old (a : Fin T.card) : Fin C.size := (e a).val
  let val := fun (U : Finset (Fin n)) (a : Fin T.card) => C.gateVal U (old a) = true
  let holds := fun (B : Finset (Fin n)) (F : Finset (Fin T.card)) (U : Finset (Fin n)) =>
    (∃ v ∈ B, v ∈ U) ∨ ∃ a ∈ F, val U a
  have represent (i : Fin C.size) :
      ∃ B F, (∀ a ∈ F, old a ≤ i) ∧ ∀ U ∈ D, C.gateVal U i = true ↔ holds B F U := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      by_cases hi : i ∈ S
      · obtain ⟨B,F,ltF,hF⟩ := hS i hi
        have ex : ∀ j : {j // j ∈ F}, ∃ B' F', (∀ a ∈ F', old a ≤ j.val) ∧
            ∀ U ∈ D, C.gateVal U j.val = true ↔ holds B' F' U :=
          fun j => ih j.val (ltF _ j.property)
        choose b f bounds eqs using ex
        refine ⟨B ∪ F.attach.biUnion b,F.attach.biUnion f,?_,?_⟩
        · intro a ha
          obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp ha
          exact (bounds j a hj).trans (ltF _ j.property).le
        · intro U hU
          rw [hF U hU]
          simp only [holds, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
            true_and] at *
          constructor
          · rintro (⟨v,hv,hvu⟩ | ⟨j,hj,ht⟩)
            · exact Or.inl ⟨v,Or.inl hv,hvu⟩
            · rcases (eqs ⟨j,hj⟩ U hU).mp ht with ⟨v,hv,hu⟩ | ⟨a,ha,hu⟩
              · exact Or.inl ⟨v,Or.inr ⟨⟨j,hj⟩,hv⟩,hu⟩
              · exact Or.inr ⟨a,⟨⟨j,hj⟩,ha⟩,hu⟩
          · rintro (⟨v,hv,hu⟩ | ⟨a,⟨j,ha⟩,hu⟩)
            · rcases hv with hv | ⟨j,hj⟩
              · exact Or.inl ⟨v,hv,hu⟩
              · exact Or.inr ⟨j.val,j.property,(eqs j U hU).mpr (Or.inl ⟨v,hj,hu⟩)⟩
            · exact Or.inr ⟨j.val,j.property,(eqs j U hU).mpr (Or.inr ⟨a,ha,hu⟩)⟩
      · let a := e.symm ⟨i,Finset.mem_compl.mpr hi⟩
        have ha : old a = i := congrArg Subtype.val (e.apply_symm_apply _)
        refine ⟨∅,{a},by simpa using ha.le,?_⟩
        intro U _
        simp [holds,val,ha]
  choose b f bounds eqs using represent
  let vars := fun (B : Finset (Fin n)) (F : Finset (Fin C.size)) => B ∪ F.biUnion b
  let gates := fun (F : Finset (Fin C.size)) => F.biUnion f
  have substSide (B F U) (hU : U ∈ D) :
      holds (vars B F) (gates F) U ↔
        (∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, C.gateVal U j = true := by
    simp only [holds,vars,gates,Finset.mem_union,Finset.mem_biUnion]
    constructor
    · rintro (⟨v,hv,hu⟩ | ⟨a,⟨j,hj,ha⟩,hu⟩)
      · rcases hv with hv | ⟨j,hj,hv⟩
        · exact Or.inl ⟨v,hv,hu⟩
        · exact Or.inr ⟨j,hj,(eqs j U hU).mpr (Or.inl ⟨v,hv,hu⟩)⟩
      · exact Or.inr ⟨j,hj,(eqs j U hU).mpr (Or.inr ⟨a,ha,hu⟩)⟩
    · rintro (⟨v,hv,hu⟩ | ⟨j,hj,ht⟩)
      · exact Or.inl ⟨v,Or.inl hv,hu⟩
      · rcases (eqs j U hU).mp ht with ⟨v,hv,hu⟩ | ⟨a,ha,hu⟩
        · exact Or.inl ⟨v,Or.inr ⟨j,hj,hv⟩,hu⟩
        · exact Or.inr ⟨a,⟨j,hj,ha⟩,hu⟩
  let K : AndCountCircuit n := {
    size := T.card
    leftVars := fun a => vars (C.leftVars (old a)) (C.leftGates (old a))
    leftGates := fun a => gates (C.leftGates (old a))
    rightVars := fun a => vars (C.rightVars (old a)) (C.rightGates (old a))
    rightGates := fun a => gates (C.rightGates (old a))
    outVars := vars C.outVars C.outGates
    outGates := gates C.outGates }
  have earlier (a : Fin T.card) (F : Finset (Fin C.size))
      (hF : ∀ j ∈ F, j < old a) : ∀ t ∈ gates F, t < a := by
    intro t ht
    obtain ⟨j,hj,htj⟩ := Finset.mem_biUnion.mp ht
    apply e.lt_iff_lt.mp
    exact (bounds j t htj).trans_lt (hF j hj)
  have wk : K.WellFormed := fun a =>
    ⟨earlier a _ (wf (old a)).1, earlier a _ (wf (old a)).2⟩
  refine ⟨K,wk,?_,?_⟩
  · change Sᶜ.card + S.card ≤ C.size
    simp
  intro U hU
  have agree (a : Fin T.card) : K.gateVal U a = C.gateVal U (old a) := by
    induction a using WellFoundedLT.induction with
    | ind a ih =>
      have side (B F) (hf : ∀ j ∈ F, j < old a) :
          sideTrue U (vars B F) (gates F) a (K.gateVal U) =
          sideTrue U B F (old a) (C.gateVal U) := by
        apply decide_eq_decide.mpr
        refine Iff.trans ?_ ((substSide B F U hU).trans ?_)
        · unfold holds val
          constructor
          · rintro (h | ⟨j,hj,hlt,ht⟩)
            · exact Or.inl h
            · exact Or.inr ⟨j,hj,ih j hlt ▸ ht⟩
          · rintro (h | ⟨j,hj,ht⟩)
            · exact Or.inl h
            · have hlt := earlier a F hf j hj
              exact Or.inr ⟨j,hj,hlt,(ih j hlt).symm ▸ ht⟩
        · exact or_congr_right ⟨fun ⟨j,hj,ht⟩ => ⟨j,hj,hf j hj,ht⟩,
            fun ⟨j,hj,_,ht⟩ => ⟨j,hj,ht⟩⟩
      rw [gateVal_unfold K,gateVal_unfold C]
      exact congrArg₂ Bool.and (side _ _ (wf (old a)).1) (side _ _ (wf (old a)).2)
  apply decide_eq_decide.mpr
  refine Iff.trans ?_ (substSide _ _ U hU)
  change ((∃ v ∈ K.outVars, v ∈ U) ∨ ∃ j ∈ K.outGates, K.gateVal U j = true) ↔ _
  simp only [agree,holds,val,K]
end PEqualNP.Outside
