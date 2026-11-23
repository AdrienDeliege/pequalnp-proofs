import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.PrivateCut

-- Expanding the largest private wire removes one available gate and
-- adds at most one wire to the frontier, including when wires are shared.
lemma frontier {α : Type*} [DecidableEq α]
    (S : Finset α) (val : Finset α → ℕ → Prop) (P : Finset ℕ)
    (leaves : ℕ → Prop) (forces : Finset ℕ → ℕ → Prop)
    (hexit : ∀ w, leaves w → ∃ p ∉ S, ∀ X : Finset α, p ∈ X → val X w)
    (hstep : ∀ B w, forces B w → ∀ X, (∀ b ∈ B, val X b) → val X w)
    (expand : ∀ w, leaves w ∨ (w ∈ P ∧ ∃ B : Finset ℕ, B.card ≤ 2 ∧ (∀ b ∈ B, b < w) ∧ forces B w))
    (R T : Finset ℕ)
    (hr : ∀ w ∈ T, ∀ p ∈ P, p ≤ w → p ∈ R ∨ leaves w) :
    ∃ X : Finset α, Disjoint X S ∧ X.card ≤ T.card + R.card ∧ ∀ w ∈ T, val X w := by
  classical
  by_cases done : ∀ w ∈ T, leaves w
  · choose f hf using fun w : T => hexit w (done w w.property)
    let X := Finset.univ.image f
    refine ⟨X, Finset.disjoint_left.mpr ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hp
      exact (hf w).1
    · have h := Finset.card_image_le (f := f) (s := Finset.univ)
      simp at h
      exact h.trans (Nat.le_add_right _ _)
    · intro w hw
      exact (hf ⟨w, hw⟩).2 X (Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩)
  · let A := T.filter fun w => ¬ leaves w
    have hA : A.Nonempty := by
      push Not at done
      obtain ⟨w, hw, hn⟩ := done
      exact ⟨w, Finset.mem_filter.mpr ⟨hw,hn⟩⟩
    let w := A.max' hA
    have hm : w ∈ A := Finset.max'_mem _ _
    obtain ⟨hw, hn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hp,B,hb,he,hs⟩ := (expand w).resolve_left hn
    have hwR := (hr w hw w hp le_rfl).resolve_right hn
    let U := T.erase w ∪ B
    have hR : ∀ q ∈ U, ∀ p ∈ P, p ≤ q → p ∈ R.erase w ∨ leaves q := by
      intro q hq p hp' hl
      by_cases hL : leaves q
      · exact Or.inr hL
      left
      rcases Finset.mem_union.mp hq with h | h
      · obtain ⟨hne,hT⟩ := Finset.mem_erase.mp h
        have hle := Finset.le_max' A q (Finset.mem_filter.mpr ⟨hT,hL⟩)
        change q ≤ w at hle
        exact Finset.mem_erase.mpr ⟨by omega, (hr q hT p hp' hl).resolve_right hL⟩
      · have hlt := he q h
        exact Finset.mem_erase.mpr ⟨by omega,(hr w hw p hp' (by omega)).resolve_right hn⟩
    obtain ⟨X, hXS, hcard, hval⟩ := frontier S val P leaves forces hexit hstep expand (R.erase w) U hR
    refine ⟨X,hXS,?_,?_⟩
    · have hu := Finset.card_union_le (T.erase w) B
      have htcard := Finset.card_erase_add_one hw
      have hrcard := Finset.card_erase_add_one hwR
      change X.card ≤ (T.erase w ∪ B).card + _ at hcard
      omega
    · intro q hq
      by_cases eq : q = w
      · subst q
        exact hstep B w hs X fun b h => hval b (Finset.mem_union_right _ h)
      · exact hval q (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hq⟩))
termination_by R.card
decreasing_by exact Finset.card_erase_lt_of_mem hwR

open PEqualNP.CircuitLowerBounds


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

end PEqualNP.Outside.PrivateCut

open PEqualNP.Outside.PrivateCut in
theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  intro n k c o S C hmono hsingle hzero hck hcS
  by_contra! hbad
  let W (x : Fin n → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
  let single (p : Fin n) := fun q : Fin n => decide (q = p)
  let supp (w : ℕ) := Finset.univ.filter (fun p : Fin n => W (single p) w = true)
  let J := (Finset.range C.size).filter fun j => supp (n+j) ⊆ S ∧ 2 ≤ (supp (n+j)).card
  change J.card < c at hbad
  let P := J.image (fun j => n+j)
  have hpc : P.card ≤ J.card := Finset.card_image_le
  let V (X : Finset (Fin n)) (w : ℕ) := ∀ p ∈ S, p ∉ X →
    W (single p) w = true → W (fun q => decide (q ∈ X ∧ q ∉ S)) w = true
  let L := fun w => ¬ (supp w ⊆ S ∧ 2 ≤ (supp w).card)
  have mono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨hop,hlen⟩ := hmono g hg
    exact ⟨by simpa using hop, by omega⟩
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  have he : ∀ w, L w → ∃ p ∉ (∅ : Finset (Fin n)), ∀ X : Finset (Fin n), p ∈ X → V X w := by
    intro w hw
    by_cases hs : supp w ⊆ S
    · have hle : (supp w).card ≤ 1 := by
        change ¬ (_ ∧ _) at hw
        by_contra! hh
        exact hw ⟨hs,hh⟩
      by_cases hne : (supp w).Nonempty
      · obtain ⟨a,ha⟩ := hne
        refine ⟨a,by simp,?_⟩
        intro X haX p _ hp ht
        have hps : p ∈ supp w := Finset.mem_filter.mpr ⟨by simp,ht⟩
        have eq := Finset.card_le_one.mp hle p hps a ha
        exact (hp (eq ▸ haX)).elim
      · obtain ⟨a,_⟩ := hn
        exact ⟨a,by simp,fun X _ p _ _ ht => (hne ⟨p,Finset.mem_filter.mpr ⟨by simp,ht⟩⟩).elim⟩
    · obtain ⟨a,ha,haS⟩ := Finset.not_subset.mp hs
      refine ⟨a,by simp,?_⟩
      intro X haX p _ _ _
      apply wires_mono C mono (single a) _ _ w (Finset.mem_filter.mp ha).2
      intro u hu
      have eq : u = a := of_decide_eq_true hu
      simpa [eq] using And.intro haX haS
  let F (B : Finset ℕ) (w : ℕ) := ∀ X, (∀ b ∈ B, V X b) → V X w
  have expand : ∀ w, L w ∨ (w ∈ P ∧ ∃ B : Finset ℕ, B.card ≤ 2 ∧ (∀ b ∈ B, b < w) ∧ F B w) := by
    intro w
    by_cases hL : L w
    · exact Or.inl hL
    have hpriv : supp w ⊆ S ∧ 2 ≤ (supp w).card := Classical.byContradiction hL
    by_cases hi : w < n
    · have hsub : supp w ⊆ {⟨w,hi⟩} := by
        intro p hp
        have hh := (Finset.mem_filter.mp hp).2
        change (C.wires _).getD w false = true at hh
        rw [wires_input C _ w hi] at hh
        exact Finset.mem_singleton.mpr (of_decide_eq_true hh).symm
      have hcar := Finset.card_le_card hsub
      simp at hcar
      have := hpriv.2
      omega
    by_cases ho : n + C.gates.length ≤ w
    · have hem : supp w = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := (Finset.mem_filter.mp hp).2
        change (C.wires _).getD w false = true at hh
        rw [wires_oob C _ w ho] at hh
        contradiction
      simp [hem] at hpriv
    let j := w-n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : n+j=w := by dsimp [j]; omega
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨hop, hlen⟩ := hmono g (List.mem_of_getElem? hg)
    let B := g.inputs.toFinset.filter (fun i => i < w)
    have hp : w ∈ P := Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hw.symm ▸ hpriv⟩,hw⟩
    refine Or.inr ⟨hp,B,?_,?_,?_⟩
    · have h1 := Finset.card_filter_le g.inputs.toFinset (fun i => i < w)
      exact h1.trans (g.inputs.toFinset_card_le.trans hlen.le)
    · exact fun b hb => (Finset.mem_filter.mp hb).2
    · intro X hB p hpS hpX hval
      change (C.wires _).getD w false = true at hval ⊢
      rw [← hw, wires_gate_ofFn C _ j g hg] at hval ⊢
      apply gateOp_mono _ hop _ _ _ _ hval
      intro i hmem htrue
      by_cases hl : i < n+j
      · simp only [hl, ↓reduceIte] at htrue ⊢
        exact hB i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem,hw ▸ hl⟩) p hpS hpX htrue
      · simp [hl] at htrue
  obtain ⟨X,_,hX,hv⟩ := frontier ∅ V P L F he (fun _ _ h => h) expand P {o} (fun _ _ _ hp _ => Or.inl hp)
  simp at hX
  have hsmall : X.card < S.card := by omega
  have hmiss : ¬ S ⊆ X := fun h => (Nat.not_le_of_gt hsmall) (Finset.card_le_card h)
  obtain ⟨p,hp,hpX⟩ := Finset.not_subset.mp hmiss
  have hone := hv o (by simp) p hp hpX ((hsingle p).mpr hp)
  have hz := hzero (fun q => decide (q ∈ X ∧ q ∉ S))
  have hsub : (Finset.univ.filter (fun q : Fin n => decide (q ∈ X ∧ q ∉ S) = true)) ⊆ X :=
    fun q h => (of_decide_eq_true (Finset.mem_filter.mp h).2).1
  have hfalse := hz ((Finset.card_le_card hsub).trans (by omega)) (fun q h => by simp [h])
  change (C.wires _).getD o false = true at hone
  rw [hfalse] at hone
  contradiction
