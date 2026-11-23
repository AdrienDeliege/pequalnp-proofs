import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta717
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def signal (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [signal v g]) w

private lemma runLen (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

private lemma runPrefix (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

private lemma appendSame (a b : List Bool) (v : Bool) (n : ℕ) (hlen : a.length = b.length)
    (h : ∀ i, i ≠ n → a.getD i false = b.getD i false) :
    ∀ i, i ≠ n → (a ++ [v]).getD i false = (b ++ [v]).getD i false := by
  intro i hi
  by_cases lt : i < a.length
  · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (hlen ▸ lt),h i hi]
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen]

private lemma avoid (gs : List Gate) (n : ℕ) (hn : ∀ g ∈ gs, n ∉ g.inputs)
    (a b : List Bool) (hlen : a.length = b.length)
    (h : ∀ i, i ≠ n → a.getD i false = b.getD i false) :
    ∀ i, i ≠ n → (run gs a).getD i false = (run gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have eq : signal a g = signal b g := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hn g (by simp) (e ▸ hi))
    change ∀ i, i ≠ n → (run gs (a ++ [signal a g])).getD i false =
      (run gs (b ++ [signal b g])).getD i false
    rw [eq]
    exact ih (fun k hk => hn k (by simp [hk])) _ _ (by simp [hlen]) (appendSame _ _ _ n hlen h)

private def idx (t n i : ℕ) := if i < t then i else if i = t then n else i-1
private def shiftGate (t n : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (idx t n)⟩

private lemma lookup (L R : List Bool) (n : ℕ) (hn : n < L.length) (i : ℕ) :
    (L ++ R).getD (idx L.length n i) false =
    (L ++ (L.getD n false :: R)).getD i false := by
  by_cases lt : i < L.length
  · simp only [idx,lt,ite_true,List.getD_append _ _ _ _ lt]
  by_cases eq : i = L.length
  · subst i
    have key : idx L.length n L.length = n := by simp [idx]
    rw [key,List.getD_append _ _ _ _ hn,List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · obtain ⟨k,hk⟩ : ∃ k, i = L.length + (k+1) := ⟨i-L.length-1,by omega⟩
    subst i
    have key : idx L.length n (L.length+(k+1)) = L.length+k := by simp [idx]
    rw [key,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
    simp

private lemma simulate (gs : List Gate) (L R : List Bool) (n : ℕ) (hn : n < L.length) :
    ∀ i, (run (gs.map (shiftGate L.length n)) (L ++ R)).getD (idx L.length n i) false =
      (run gs (L ++ (L.getD n false :: R))).getD i false := by
  induction gs generalizing R with
  | nil => exact lookup L R n hn
  | cons g gs ih =>
    let v := signal (L ++ (L.getD n false :: R)) g
    have he : signal (L ++ R) (shiftGate L.length n g) = v := by
      simp only [signal,shiftGate,List.map_map,v]
      apply congrArg g.op.eval
      exact List.map_congr_left (fun i _ => lookup L R n hn i)
    change ∀ i, (run _ ((L ++ R) ++ [signal (L ++ R) _])).getD _ false =
      (run gs ((L ++ (L.getD n false :: R)) ++ [v])).getD i false
    rw [he]
    simpa only [List.append_assoc,List.cons_append] using ih (R ++ [v])

private lemma splitUnique (gs : List Gate) (j n : ℕ) (h : Gate) (hj : gs[j]? = some h)
    (uniq : ∀ k g, gs[k]? = some g → n ∈ g.inputs → k = j) :
    ∃ P Q, gs = P ++ h :: Q ∧ P.length = j ∧
      (∀ g ∈ P, n ∉ g.inputs) ∧ (∀ g ∈ Q, n ∉ g.inputs) := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero =>
      simp at hj
      subst h
      refine ⟨[],gs,rfl,rfl,by simp,?_⟩
      intro g hg hn
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hg
      have := uniq (k+1) g (by simpa using hk) hn
      omega
    | succ j =>
      obtain ⟨P,Q,hg,hp,ha,hb⟩ := ih j (by simpa using hj) (by
        intro k g hk hn
        have := uniq (k+1) g (by simpa using hk) hn
        omega)
      refine ⟨a::P,Q,by simp [hg],by simp [hp],?_,hb⟩
      intro g hm hn
      rcases List.mem_cons.mp hm with rfl | hm
      · have := uniq 0 g (by simp) hn
        omega
      · exact ha _ hm hn

end PEqualNP.Outside.LMeta717

namespace PEqualNP.Outside
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LMeta717

theorem L_meta_717 : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ y y' : Fin n → Bool, g y ≠ g y') → PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' → (∀ x : Fin (n + 1) → Bool, C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → C.size ≤ C'.size) → ¬ ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some h ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n ∈ h.inputs ∧ ∀ (j' : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j := by
  classical
  intro n g C nonconst fan computes minimal
  rintro ⟨j,h,hj,hop,reads,unique⟩
  obtain ⟨P,Q,split,hp,hP,hQ⟩ := splitUnique _ j n h hj unique
  let X (y : Fin n → Bool) (b : Bool) := List.ofFn y ++ [b]
  have lenX (y : Fin n → Bool) (b : Bool) : (X y b).length = n+1 := by simp [X]
  have bit (y : Fin n → Bool) (b : Bool) : (X y b).getD n false = b := by
    simp [X,List.getD_append_right]
  have spec (y : Fin n → Bool) (b : Bool) : C.eval (X y b) = xor b (g y) := by
    have H := computes (Fin.lastCases b y)
    rw [List.ofFn_succ_last] at H
    simpa [X] using H
  have out : C.output ≠ n := by
    intro bad
    obtain ⟨a,b,hab⟩ := nonconst
    have fixed (y : Fin n → Bool) : g y = false := by
      have hv := spec y false
      change (run C.gates (X y false)).getD C.output false = _ at hv
      rw [bad,runPrefix _ _ (by rw [lenX]; omega),bit] at hv
      simpa using hv.symm
    exact hab ((fixed a).trans (fixed b).symm)
  let pre (y : Fin n → Bool) (b : Bool) := run P (X y b)
  have prelen (y : Fin n → Bool) (b : Bool) : (pre y b).length = n+1+j := by
    simp [pre,runLen,lenX,hp]
  have prebit (y : Fin n → Bool) (b : Bool) : (pre y b).getD n false = b := by
    change (run P (X y b)).getD n false = b
    rw [runPrefix _ _ (by rw [lenX]; omega),bit]
  have output (y : Fin n → Bool) (b : Bool) :
      (run Q (pre y b ++ [signal (pre y b) h])).getD C.output false = xor b (g y) := by
    have H := spec y b
    change (run C.gates _).getD C.output false = _ at H
    simpa only [split,run,List.foldl_append,List.foldl_cons,pre] using H
  have diff (y : Fin n → Bool) : signal (pre y false) h ≠ signal (pre y true) h := by
    intro same
    have initial : ∀ i, i ≠ n → (X y false).getD i false = (X y true).getD i false := by
      intro i hi
      by_cases lt : i < n
      · unfold X
        have hi : i < (List.ofFn y).length := by simpa using lt
        rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hi]
      · rw [List.getD_eq_default _ _ (by rw [lenX]; omega),List.getD_eq_default _ _ (by rw [lenX]; omega)]
    have hpre := avoid P n hP _ _ (by rw [lenX,lenX]) initial
    have hsame := appendSame (pre y false) (pre y true) (signal (pre y true) h) n
      (by rw [prelen,prelen]) hpre
    have H := avoid Q n hQ _ _ (by simp [prelen]) hsame C.output out
    rw [← same] at H
    conv at H => rhs; rw [same]
    rw [output,output] at H
    cases eq : g y <;> simp [eq] at H
  have identity (y : Fin n → Bool) (b : Bool) : signal (pre y b) h = b := by
    have sep := diff y
    rcases hop with hand | hor
    · have hf : signal (pre y false) h = false := by
        simp only [signal,hand,GateOp.eval,List.all_eq_false]
        exact ⟨false,List.mem_map.mpr ⟨n,reads,prebit y false⟩,by decide⟩
      cases b
      · exact hf
      · cases ht : signal (pre y true) h <;> simp_all
    · have ht : signal (pre y true) h = true := by
        simp only [signal,hor,GateOp.eval,List.any_eq_true]
        exact ⟨true,List.mem_map.mpr ⟨n,reads,prebit y true⟩,rfl⟩
      cases b
      · cases hf : signal (pre y false) h <;> simp_all
      · exact ht
  let t := n+1+j
  let K : Circuit := ⟨P ++ Q.map (shiftGate t n), idx t n C.output⟩
  have legal : FanInTwo K := by
    intro gate hm
    change gate ∈ P ++ Q.map _ at hm
    rcases List.mem_append.mp hm with ha | hb
    · exact fan gate (by simp [split,ha])
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hb
      simpa [shiftGate] using fan u (by simp [split,hu])
  have agree (x : Fin (n+1) → Bool) :
      K.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)) := by
    let y := fun i : Fin n => x i.castSucc
    let b := x (Fin.last n)
    have he : List.ofFn x = X y b := List.ofFn_succ_last
    have sim := simulate Q (pre y b) [] n (by rw [prelen]; omega) C.output
    rw [prelen,prebit] at sim
    simp only [List.append_nil] at sim
    rw [he]
    change (run (P ++ Q.map _) (X y b)).getD _ false = _
    have lhs : run (P ++ Q.map (shiftGate t n)) (X y b) =
        run (Q.map (shiftGate t n)) (pre y b) := List.foldl_append
    rw [lhs]
    exact sim.trans (by simpa only [identity] using output y b)
  have small := minimal K legal agree
  simp [K,Circuit.size,split] at small
end PEqualNP.Outside
