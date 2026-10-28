import OAI.Analysis.PDE.Weak.Elliptic.Linear
import OAI.Analysis.PDE.Weak.Elliptic.H1Neighborhood

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A finite hierarchy of actual local weak L² derivatives. -/
def WeakRegularity (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) :
    ℕ → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) → Prop
  | 0, _ => True
  | k + 1, u => ∀ i : Fin (m + 1), ∃ g : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) u g ∧ WeakRegularity Ω k g

/-- The derivative hierarchy retaining the genuine H¹ graph at each node. -/
def H1Regularity (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : ℕ → H1Pair m → Prop
  | 0, _ => True
  | k + 1, p => ∀ i : Fin (m + 1), ∃ q : H1Pair m, q ∈ H1Zero univ ∧
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.1 q.1 ∧
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.2 q.2 ∧ H1Regularity Ω k q

omit [CompleteSpace E] in
theorem WeakRegularity.mono_domain {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {k : ℕ} {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) (hsub : Ω' ⊆ Ω) : WeakRegularity Ω' k u := by
  induction k generalizing u with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    exact ⟨g, hd.mono volume hsub, ih hg⟩

omit [CompleteSpace E] in
theorem WeakRegularity.pred {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω (k + 1) u) : WeakRegularity Ω k u := by
  induction k generalizing u with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    exact ⟨g, hd, ih hg⟩

omit [CompleteSpace E] in
theorem WeakRegularity.congr_on {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u w : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) (heq : ∀ᵐ x ∂volume, x ∈ Ω → u x = w x) :
    WeakRegularity Ω k w := by
  cases k with
  | zero => trivial
  | succ k =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    exact ⟨g, hd.congr_on volume heq (Eventually.of_forall fun _ _ ↦ rfl), hg⟩

omit [CompleteSpace E] in
theorem WeakRegularity.add {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u w : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) (hw : WeakRegularity Ω k w) :
    WeakRegularity Ω k (u + w) := by
  induction k generalizing u w with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    obtain ⟨z, he, hz⟩ := hw i
    exact ⟨g + z, hd.add_Lp volume he, ih hg hz⟩

omit [CompleteSpace E] in
theorem WeakRegularity.neg {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) : WeakRegularity Ω k (-u) := by
  induction k generalizing u with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    exact ⟨-g, hd.neg_Lp volume, ih hg⟩

omit [CompleteSpace E] in
theorem WeakRegularity.sub {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u w : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) (hw : WeakRegularity Ω k w) :
    WeakRegularity Ω k (u - w) := by
  simpa only [sub_eq_add_neg] using hu.add hw.neg

omit [CompleteSpace E] in
theorem WeakRegularity.zero (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ) :
    WeakRegularity Ω k (0 : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    intro i
    exact ⟨0, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.zero_Lp volume Ω (Pi.single i 1), ih⟩

omit [CompleteSpace E] in
theorem WeakRegularity.finset_sum {ι : Type*} (s : Finset ι)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    (u : ι → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hu : ∀ i ∈ s, WeakRegularity Ω k (u i)) : WeakRegularity Ω k (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OAI.Analysis.PDE.Weak.WeakRegularity.zero (E := E) Ω k
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)))

theorem WeakRegularity.map
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u) (L : E →L[ℝ] F) :
    WeakRegularity Ω k (L.compLp u) := by
  induction k generalizing u with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    exact ⟨L.compLp g, hd.map_Lp volume L, ih hg⟩

theorem H1Regularity.mono_domain {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {k : ℕ} {p : H1Pair m} (hp : H1Regularity Ω k p) (hsub : Ω' ⊆ Ω) :
    H1Regularity Ω' k p := by
  induction k generalizing p with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨q, hq, hdv, hdg, hr⟩ := hp i
    exact ⟨q, hq, hdv.mono volume hsub, hdg.mono volume hsub, ih hr⟩

theorem H1Regularity.value {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ} {p : H1Pair m}
    (hp : H1Regularity Ω k p) : WeakRegularity Ω k p.1 := by
  induction k generalizing p with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨q, -, hdv, -, hr⟩ := hp i
    exact ⟨q.1, hdv, ih hr⟩

theorem H1Regularity.gradient {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ} {p : H1Pair m}
    (hp : H1Regularity Ω k p) : WeakRegularity Ω k p.2 := by
  induction k generalizing p with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨q, -, -, hdg, hr⟩ := hp i
    exact ⟨q.2, hdg, ih hr⟩

end OAI.Analysis.PDE.Weak
