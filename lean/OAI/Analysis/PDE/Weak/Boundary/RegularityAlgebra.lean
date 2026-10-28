import OAI.Analysis.PDE.Weak.Boundary.SmoothBounded
import OAI.Analysis.PDE.Weak.Elliptic.RegularityProduct

/-! A representative-independent interface for the finite weak derivative
hierarchy. All witnesses are genuine global L² functions. -/

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def FunctionWeakRegularity (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ)
    (u : OAI.Analysis.PDE.Variational.CellCoordinates m → E) : Prop :=
  ∃ U : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
    (∀ᵐ x ∂volume, x ∈ Ω → u x = U x) ∧ WeakRegularity Ω k U

omit [CompleteSpace E] in
theorem WeakRegularity.function {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))} (hu : WeakRegularity Ω k u) :
    FunctionWeakRegularity Ω k u := ⟨u, Eventually.of_forall (fun _ _ => rfl), hu⟩

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.congr_on {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u)
    (he : ∀ᵐ x ∂volume, x ∈ Ω → u x = v x) : FunctionWeakRegularity Ω k v := by
  obtain ⟨U, hU, hr⟩ := hu
  refine ⟨U, ?_, hr⟩
  filter_upwards [hU, he] with x hx hy
  exact fun hxs => (hy hxs).symm.trans (hx hxs)

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.toLp {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u) (hm : MemLp u 2 volume) :
    WeakRegularity Ω k (hm.toLp u) := by
  obtain ⟨U, hU, hr⟩ := hu
  apply hr.congr_on
  filter_upwards [hU, hm.coeFn_toLp] with x hx hy
  exact fun hxs => (hx hxs).symm.trans hy.symm

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.mono_domain {Ω V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u) (hs : V ⊆ Ω) :
    FunctionWeakRegularity V k u := by
  obtain ⟨U, hU, hr⟩ := hu
  refine ⟨U, ?_, hr.mono_domain hs⟩
  filter_upwards [hU] with x hx
  exact fun hxs => hx (hs hxs)

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.add {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u)
    (hv : FunctionWeakRegularity Ω k v) : FunctionWeakRegularity Ω k (fun x => u x + v x) := by
  obtain ⟨U, hU, hr⟩ := hu
  obtain ⟨V, hV, hs⟩ := hv
  refine ⟨U + V, ?_, hr.add hs⟩
  filter_upwards [hU, hV, Lp.coeFn_add U V] with x hx hy hz
  exact fun hxs => by rw [hx hxs, hy hxs, hz]; rfl

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.neg {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u) :
    FunctionWeakRegularity Ω k (fun x => -u x) := by
  obtain ⟨U, hU, hr⟩ := hu
  refine ⟨-U, ?_, hr.neg⟩
  filter_upwards [hU, Lp.coeFn_neg U] with x hx hy
  exact fun hxs => by rw [hx hxs, hy]; rfl

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.sub {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u)
    (hv : FunctionWeakRegularity Ω k v) : FunctionWeakRegularity Ω k (fun x => u x - v x) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.zero (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ) :
    FunctionWeakRegularity Ω k (fun _ => (0 : E)) := by
  refine ⟨0, ?_, OAI.Analysis.PDE.Weak.WeakRegularity.zero Ω k⟩
  filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))] with x hx
  exact fun _ => hx.symm

omit [CompleteSpace E] in
theorem FunctionWeakRegularity.finset_sum {ι : Type*} (s : Finset ι)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ} (u : ι → OAI.Analysis.PDE.Variational.CellCoordinates m → E)
    (hu : ∀ i ∈ s, FunctionWeakRegularity Ω k (u i)) :
    FunctionWeakRegularity Ω k (fun x => ∑ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using OAI.Analysis.PDE.Weak.FunctionWeakRegularity.zero (E := E) Ω k
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem FunctionWeakRegularity.map {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u) (L : E →L[ℝ] F) :
    FunctionWeakRegularity Ω k (fun x => L (u x)) := by
  obtain ⟨U, hU, hr⟩ := hu
  refine ⟨L.compLp U, ?_, hr.map L⟩
  filter_upwards [hU, L.coeFn_compLp U] with x hx hy
  exact fun hxs => (congrArg L (hx hxs)).trans hy.symm

theorem FunctionWeakRegularity.operator_mul {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → E} (hu : FunctionWeakRegularity Ω k u)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → E →L[ℝ] F) (hA : SmoothBounded A) :
    FunctionWeakRegularity Ω k (fun x => A x (u x)) := by
  obtain ⟨U, hU, hr⟩ := hu
  obtain ⟨M, hM⟩ := hA.bound
  refine ⟨fieldMultiplierCLM A hA.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) U, ?_, hr.operator_mul A hA hM⟩
  filter_upwards [hU, fieldMultiplierCLM_ae A hA.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hM) U] with x hx hy
  exact fun hxs => (congrArg (A x) (hx hxs)).trans hy.symm

theorem FunctionWeakRegularity.scalar_mul {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : FunctionWeakRegularity Ω k u)
    (a : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (ha : SmoothBounded a) :
    FunctionWeakRegularity Ω k (fun x => a x * u x) := by
  let L : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)
  have he := hu.operator_mul (fun x => L (a x)) (ha.map L)
  simpa only [L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    smul_apply, smul_eq_mul] using he

end OAI.Analysis.PDE.Weak
