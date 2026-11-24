import Mathlib
import PEqualNP.Defs

-- Generic circuit semantics and encoding lemmas adapted from L_meta_2466 and Nathan Pollock’s L_meta_1942.

namespace PEqualNP.Outside.L_meta_3497


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover



private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def families {n : ℕ} (op : GateOp) : List (Finset (Finset (Fin n))) → Finset (Finset (Fin n))
  | [u,v] => if op.eval [false,true] then u.biUnion (fun s => v.image (fun t => s ∪ t)) else u ∪ v
  | _ => {∅}

private def Hit {n : ℕ} (x : List Bool) (s : Finset (Fin n)) : Prop :=
  ∃ i ∈ s, x.getD i.val false = true

private lemma cross_iff {n : ℕ} (x : List Bool) (u v : Finset (Finset (Fin n))) :
    (∀ s ∈ u.biUnion (fun a => v.image (fun b => a ∪ b)), Hit x s) ↔
      (∀ a ∈ u, Hit x a) ∨ (∀ b ∈ v, Hit x b) := by
  classical
  constructor
  · intro h
    by_cases ok : ∀ a ∈ u, Hit x a
    · exact Or.inl ok
    · push Not at ok
      obtain ⟨a,ha,bad⟩ := ok
      right
      intro b hb
      obtain ⟨i,hi,on⟩ := h (a ∪ b) (Finset.mem_biUnion.mpr
        ⟨a,ha,Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩)
      rcases Finset.mem_union.mp hi with hia | hib
      · exact False.elim (bad ⟨i,hia,on⟩)
      · exact ⟨i,hib,on⟩
  · intro ok s hs
    obtain ⟨a,ha,h⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    rcases ok with left | right
    · obtain ⟨i,hi,on⟩ := left a ha
      exact ⟨i,Finset.mem_union_left _ hi,on⟩
    · obtain ⟨i,hi,on⟩ := right b hb
      exact ⟨i,Finset.mem_union_right _ hi,on⟩

end PEqualNP.Outside.L_meta_3497
open PEqualNP.Outside.L_meta_3497 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C mono inputs
  have sources (k : Fin C.size) := inputs k.val (row C k) (List.getElem?_eq_getElem k.isLt)
  have valid : PEqualNP.TopForm.IsAO2 n C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      exact (mono g hg).1
    · intro j hj i hi
      let k : Fin C.size := ⟨j,hj⟩
      obtain ⟨a,b,eq,ab,bl⟩ := sources k
      have ge : gateAt C j = row C k := List.getD_eq_getElem _ _ hj
      rw [ge,eq] at hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact lt_trans ab bl
      · exact (List.mem_singleton.mp hi) ▸ bl
    · intro g hg
      obtain ⟨j,hj,hg'⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,eq,_,_⟩ := sources ⟨j,hj⟩
      subst g
      change C.gates[j].inputs = [a,b] at eq
      simp [eq]
  let bad : Finset (Finset (Fin n)) := {∅}
  let seeds := List.ofFn (fun i : Fin n => ({ {i} } : Finset (Finset (Fin n))))
  let sets := evalFrom bad families C.gates seeds
  let F := fun w : ℕ => sets.getD w bad
  have init (i : Fin n) : F i.val = {{i}} := by
    change (evalFrom bad families C.gates seeds).getD i.val bad = _
    rw [evalFrom_input _ _ _ _ _ (by simp [seeds])]
    simp [seeds]
  have recF (k : Fin C.size) : F (outWire n k) =
      families (row C k).op [F (operand C k 0),F (operand C k 1)] :=
    evalFrom_gate bad families valid seeds List.length_ofFn k
  refine ⟨F,init,?_,?_⟩
  · intro j hj
    let k : Fin C.size := ⟨j,hj⟩
    obtain ⟨a,b,eq,ab,bl⟩ := sources k
    refine ⟨a,b,eq,ab,bl,?_⟩
    have ha : operand C k 0 = a := by simp [operand,eq]
    have hb : operand C k 1 = b := by simp [operand,eq]
    have step := recF k
    rw [ha,hb] at step
    exact step
  · intro x hx w
    change (evalFrom false GateOp.eval C.gates x).getD w false = true ↔ ∀ s ∈ F w, Hit x s
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases wire_cases n C.size w with hw | ⟨k,rfl⟩ | hw
      · rw [evalFrom_input _ _ _ _ _ (hx ▸ hw),init ⟨w,hw⟩]
        simp [Hit]
      · rw [evalFrom_gate false GateOp.eval valid x hx k,recF]
        have L := ih _ (earlier valid k 0)
        have R := ih _ (earlier valid k 1)
        rcases op_kind valid k with h | h
        · rw [h]
          simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true,L,R]
          exact Finset.forall_mem_union.symm
        · rw [h]
          simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,L,R]
          exact (cross_iff x _ _).symm
      · have hlen : sets.length = n + C.size := by simp [sets,evalFrom_length,seeds,Circuit.size]
        have hval := List.getD_eq_default (evalFrom false GateOp.eval C.gates x) false
          (show (evalFrom false GateOp.eval C.gates x).length ≤ w by simpa [evalFrom_length,hx,Circuit.size] using hw)
        have hf : F w = bad := List.getD_eq_default _ _ (by omega)
        rw [hval,hf]
        simp [bad,Hit]
