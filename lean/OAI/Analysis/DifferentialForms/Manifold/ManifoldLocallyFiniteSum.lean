import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative
import OAI.Analysis.DifferentialForms.Manifold.LocallyFiniteSum

/-! # Manifold Locally Finite Sum -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

section

/-!
# Locally finite sums of genuine manifold forms

The sums are taken in the actual tangent covector space at each point. Local
finiteness gives equality with a finite sum on a neighborhood, and this equality
transports through the chart expression and the local exterior derivative.
-/

open Function Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Topology ContDiff

section DependentSupport

variable {ι X : Type*} [TopologicalSpace X] {B : X → Type*} [∀ x, Zero (B x)]

/-- Local finiteness supplies one finite support on a neighborhood even for a
field with point-dependent fibers. -/
theorem ManifoldLocallyFiniteSum.exists_finset_eventually_dependent_support (f : ι → ∀ x, B x)
    (hlf : LocallyFinite (fun i => {x | f i x ≠ 0})) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, support (fun i => f i y) ⊆ s := by
  obtain ⟨t, ht, hfin⟩ := hlf x
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [ht] with y hy
  intro i hi
  change i ∈ hfin.toFinset
  rw [hfin.mem_toFinset]
  exact ⟨y, hi, hy⟩

end DependentSupport

variable {ι E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

section

/-- Equality of fields near the inverse-chart point gives equality of their
ordinary coefficient functions near the coordinate point. -/
theorem Algebra.RawManifoldForm.inChart_congr_eventually {form other : Algebra.RawManifoldForm E M n}
    (e : OpenPartialHomeomorph M E) {y : E} (hy : y ∈ e.target)
    (heq : ∀ᶠ x in 𝓝 (e.symm y), form x = other x) :
    form.inChart e =ᶠ[𝓝 y] other.inChart e := by
  filter_upwards [(e.continuousAt_symm hy).eventually heq] with z hz
  unfold Algebra.RawManifoldForm.inChart
  rw [hz]

/-- A neighborhood equality suffices for equality of the actual manifold
exterior derivative at the point. -/
theorem Algebra.RawManifoldForm.exteriorDerivative_congr_eventually {form other : Algebra.RawManifoldForm E M n}
    {x : M} (heq : ∀ᶠ y in 𝓝 x, form y = other y) :
    form.exteriorDerivative x = other.exteriorDerivative x := by
  obtain ⟨s, hs, hopen, hx⟩ := mem_nhds_iff.mp heq
  exact Algebra.RawManifoldForm.exteriorDerivative_congr_on form other hopen (fun y hy => hs hy) hx

/-- The actual fiberwise sum of raw tangent-covector fields. -/
def Algebra.RawManifoldForm.locallyFiniteSum (form : ι → Algebra.RawManifoldForm E M n) : Algebra.RawManifoldForm E M n :=
  fun x => ∑ᶠ i, form i x

@[simp] theorem Algebra.RawManifoldForm.locallyFiniteSum_apply (form : ι → Algebra.RawManifoldForm E M n) (x : M) :
    Algebra.RawManifoldForm.locallyFiniteSum form x = ∑ᶠ i, form i x := rfl

end

section

/-- Evaluation commutes with a finite sum of genuine manifold forms. -/
theorem Algebra.SmoothManifoldForm.sum_apply (form : ι → Algebra.SmoothManifoldForm E M n) (s : Finset ι) (x : M) :
    (∑ i ∈ s, form i) x = ∑ i ∈ s, form i x :=
  map_sum (Algebra.SmoothManifoldForm.eval x) form s

theorem Algebra.SmoothManifoldForm.raw_locallyFiniteSum_eventuallyEq (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) (x : M) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x,
      Algebra.RawManifoldForm.locallyFiniteSum (fun i => (form i : Algebra.RawManifoldForm E M n)) y =
        (∑ i ∈ s, form i) y := by
  obtain ⟨s, hs⟩ := ManifoldLocallyFiniteSum.exists_finset_eventually_dependent_support
    (fun i => (form i : Algebra.RawManifoldForm E M n)) hlf x
  refine ⟨s, hs.mono ?_⟩
  intro y hy
  rw [Algebra.RawManifoldForm.locallyFiniteSum_apply, Algebra.SmoothManifoldForm.sum_apply]
  exact finsum_eq_sum_of_support_subset _ hy

/-- The actual local chart expression of the sum is smooth. -/
theorem Algebra.SmoothManifoldForm.smooth_raw_locallyFiniteSum (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) :
    Algebra.IsSmoothManifoldFormOn
      (Algebra.RawManifoldForm.locallyFiniteSum (fun i => (form i : Algebra.RawManifoldForm E M n))) univ := by
  intro e he y hy
  obtain ⟨s, hs⟩ := Algebra.SmoothManifoldForm.raw_locallyFiniteSum_eventuallyEq form hlf (e.symm y)
  have hc := Algebra.RawManifoldForm.inChart_congr_eventually e hy.1 hs
  have hsm := Derivative.smoothForm_contDiffAt_inChart (∑ i ∈ s, form i).smooth e he hy.1
  exact (hsm.congr_of_eventuallyEq hc).contDiffWithinAt

/-- A smooth form obtained by the actual fiberwise locally finite sum. -/
def Algebra.SmoothManifoldForm.locallyFiniteSum (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) : Algebra.SmoothManifoldForm E M n :=
  ⟨Algebra.RawManifoldForm.locallyFiniteSum (fun i => (form i : Algebra.RawManifoldForm E M n)),
    Algebra.SmoothManifoldForm.smooth_raw_locallyFiniteSum form hlf⟩

@[simp] theorem Algebra.SmoothManifoldForm.locallyFiniteSum_apply (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) (x : M) :
    Algebra.SmoothManifoldForm.locallyFiniteSum form hlf x = ∑ᶠ i, form i x := rfl

end

variable [IsManifold 𝓘(ℝ, E) ∞ M]

section

/-- Exterior differentiation cannot enlarge the closure of the nonzero locus. -/
theorem Algebra.RawManifoldForm.nonzero_exteriorDerivative_subset_closure (form : Algebra.RawManifoldForm E M n) :
    {x | form.exteriorDerivative x ≠ 0} ⊆ closure {x | form x ≠ 0} := by
  intro x hx
  by_contra hnot
  have hzero : ∀ᶠ y in 𝓝 x, form y = 0 := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hnot] with y hy
    by_contra hne
    exact hy (subset_closure hne)
  apply hx
  have heq := Algebra.RawManifoldForm.exteriorDerivative_congr_eventually
    (form := form) (other := (0 : Algebra.RawManifoldForm E M n)) hzero
  exact heq.trans (congrArg (fun f : Algebra.SmoothManifoldForm E M (n + 1) => f x)
    (Algebra.SmoothManifoldForm.d.map_zero))

end

theorem Algebra.SmoothManifoldForm.locallyFinite_d (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) :
    LocallyFinite (fun i => {x | Algebra.SmoothManifoldForm.d (form i) x ≠ 0}) :=
  hlf.closure.subset fun i =>
    Algebra.RawManifoldForm.nonzero_exteriorDerivative_subset_closure (form i : Algebra.RawManifoldForm E M n)

/-- The exterior differential commutes with the genuine locally finite sum. -/
theorem Algebra.SmoothManifoldForm.d_locallyFiniteSum (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) :
    Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.locallyFiniteSum form hlf) =
      Algebra.SmoothManifoldForm.locallyFiniteSum (fun i => Algebra.SmoothManifoldForm.d (form i)) (Algebra.SmoothManifoldForm.locallyFinite_d form hlf) := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  obtain ⟨s, hs⟩ := ManifoldLocallyFiniteSum.exists_finset_eventually_dependent_support
    (fun i => (form i : Algebra.RawManifoldForm E M n)) hlf x
  have heq : ∀ᶠ y in 𝓝 x, Algebra.SmoothManifoldForm.locallyFiniteSum form hlf y = (∑ i ∈ s, form i) y := by
    filter_upwards [hs] with y hy
    rw [Algebra.SmoothManifoldForm.locallyFiniteSum_apply, Algebra.SmoothManifoldForm.sum_apply]
    exact finsum_eq_sum_of_support_subset _ hy
  have hd : Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.locallyFiniteSum form hlf) x = Algebra.SmoothManifoldForm.d (∑ i ∈ s, form i) x :=
    Algebra.RawManifoldForm.exteriorDerivative_congr_eventually heq
  have hs' : support (fun i => Algebra.SmoothManifoldForm.d (form i) x) ⊆ s := by
    intro i hi
    by_contra his
    have hzero : ∀ᶠ y in 𝓝 x, form i y = 0 := by
      filter_upwards [hs] with y hy
      by_contra hne
      exact his (hy hne)
    have hz : Algebra.SmoothManifoldForm.d (form i) x = (Algebra.SmoothManifoldForm.d (0 : Algebra.SmoothManifoldForm E M n)) x :=
      Algebra.RawManifoldForm.exteriorDerivative_congr_eventually hzero
    apply hi
    change Algebra.SmoothManifoldForm.d (form i) x = 0
    rw [hz, map_zero]
    rfl
  rw [hd, map_sum, Algebra.SmoothManifoldForm.sum_apply, Algebra.SmoothManifoldForm.locallyFiniteSum_apply]
  exact (finsum_eq_sum_of_support_subset _ hs').symm

end

/-!
# Locally finite sums of open-domain manifold sections

Supports are locally finite in the actual open domain. Smoothness follows by
comparing the auxiliary extension with a finite sum near each domain point.
-/

open Function Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Topology ContDiff

variable {ι E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {U V : Opens M}

section

/-- Evaluation in the actual ambient tangent covector space. -/
def Open.SmoothOpenManifoldForm.eval (x : U) : Open.SmoothOpenManifoldForm E U n →ₗ[ℂ]
    (TangentSpace 𝓘(ℝ, E) (x : M) [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := form x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Open.SmoothOpenManifoldForm.sum_apply (form : ι → Open.SmoothOpenManifoldForm E U n) (s : Finset ι) (x : U) :
    (∑ i ∈ s, form i) x = ∑ i ∈ s, form i x := map_sum (Open.SmoothOpenManifoldForm.eval x) form s

def Open.SmoothOpenManifoldForm.rawLocallyFiniteSum (form : ι → Open.SmoothOpenManifoldForm E U n) :
    Open.RawOpenManifoldForm E U n := fun x => ∑ᶠ i, form i x

theorem Open.SmoothOpenManifoldForm.raw_locallyFiniteSum_extension_eventuallyEq
    (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) (x : U) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 (x : M),
      Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.rawLocallyFiniteSum form) y =
        (∑ i ∈ s, form i).extension y := by
  obtain ⟨s, hs⟩ := ManifoldLocallyFiniteSum.exists_finset_eventually_dependent_support
    (fun i => (form i : Open.RawOpenManifoldForm E U n)) hlf x
  refine ⟨s, ?_⟩
  rw [← U.isOpenEmbedding'.map_nhds_eq x]
  change ∀ᶠ y : U in 𝓝 x,
    Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.rawLocallyFiniteSum form) y = (∑ i ∈ s, form i).extension y
  filter_upwards [hs] with y hy
  rw [Open.openManifoldFormExtension_apply, Open.SmoothOpenManifoldForm.extension_apply, Open.SmoothOpenManifoldForm.sum_apply]
  exact finsum_eq_sum_of_support_subset _ hy

theorem Open.SmoothOpenManifoldForm.smooth_raw_locallyFiniteSum (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) :
    Algebra.IsSmoothManifoldFormOn (Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.rawLocallyFiniteSum form))
      (U : Set M) := by
  intro e he y hy
  obtain ⟨s, hs⟩ := Open.SmoothOpenManifoldForm.raw_locallyFiniteSum_extension_eventuallyEq form hlf ⟨e.symm y, hy.2⟩
  have hc := Algebra.RawManifoldForm.inChart_congr_eventually e hy.1 hs
  have hsm := LocalDerivative.smoothManifoldFormOn_contDiffAt_inChart U.isOpen
    (∑ i ∈ s, form i).smooth e he hy
  exact (hsm.congr_of_eventuallyEq hc).contDiffWithinAt

/-- The actual fiberwise sum of a family locally finite in its open domain. -/
def Open.SmoothOpenManifoldForm.locallyFiniteSum (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) :
    Open.SmoothOpenManifoldForm E U n :=
  ⟨Open.SmoothOpenManifoldForm.rawLocallyFiniteSum form, Open.SmoothOpenManifoldForm.smooth_raw_locallyFiniteSum form hlf⟩

@[simp] theorem Open.SmoothOpenManifoldForm.locallyFiniteSum_apply (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) (x : U) :
    Open.SmoothOpenManifoldForm.locallyFiniteSum form hlf x = ∑ᶠ i, form i x := rfl

theorem Open.SmoothOpenManifoldForm.locallyFinite_restrict (h : V ≤ U) (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) :
    LocallyFinite (fun i => {x : V | Open.SmoothOpenManifoldForm.restrict h (form i) x ≠ 0}) :=
  hlf.preimage_continuous (continuous_inclusion h)

/-- Restriction commutes with the locally finite sum. -/
theorem Open.SmoothOpenManifoldForm.restrict_locallyFiniteSum (h : V ≤ U) (form : ι → Open.SmoothOpenManifoldForm E U n)
    (hlf : LocallyFinite (fun i => {x : U | form i x ≠ 0})) :
    Open.SmoothOpenManifoldForm.restrict h (Open.SmoothOpenManifoldForm.locallyFiniteSum form hlf) =
      Open.SmoothOpenManifoldForm.locallyFiniteSum (fun i => Open.SmoothOpenManifoldForm.restrict h (form i)) (Open.SmoothOpenManifoldForm.locallyFinite_restrict h form hlf) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [Open.SmoothOpenManifoldForm.restrict_apply, Open.SmoothOpenManifoldForm.locallyFiniteSum_apply]

end

theorem Algebra.SmoothManifoldForm.locallyFinite_onOpen (U : Opens M) (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) :
    LocallyFinite (fun i => {x : U | Algebra.SmoothManifoldForm.onOpen U (form i) x ≠ 0}) :=
  hlf.preimage_continuous continuous_subtype_val

theorem Algebra.SmoothManifoldForm.onOpen_locallyFiniteSum (U : Opens M) (form : ι → Algebra.SmoothManifoldForm E M n)
    (hlf : LocallyFinite (fun i => {x | form i x ≠ 0})) :
    Algebra.SmoothManifoldForm.onOpen U (Algebra.SmoothManifoldForm.locallyFiniteSum form hlf) = Open.SmoothOpenManifoldForm.locallyFiniteSum
      (fun i => Algebra.SmoothManifoldForm.onOpen U (form i)) (Algebra.SmoothManifoldForm.locallyFinite_onOpen U form hlf) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rfl

end

end OAI.Analysis.DifferentialForms.Manifold
