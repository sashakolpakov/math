import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! # Smooth Cocycle Primitive -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothCocyclePrimitive

noncomputable section

section

/-! A smooth function on an overlap extends across one boundary after
multiplication by a smooth function supported inside that open set. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M]

abbrev SmoothOpenScalar (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M] (U : Opens M) :=
  C^∞⟮𝓘(ℝ, E), U; 𝓘(ℝ, ℂ), ℂ⟯

def smoothOpenScalarExtend {U : Opens M} (f : SmoothOpenScalar E U) : M → ℂ := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

theorem smoothOpenScalarExtend_apply {U : Opens M} (f : SmoothOpenScalar E U)
    (x : M) (hx : x ∈ U) : smoothOpenScalarExtend f x = f ⟨x, hx⟩ := by
  simp only [smoothOpenScalarExtend, dite_eq_left hx]

theorem smoothOpenScalarExtend_contMDiffOn {U : Opens M} (f : SmoothOpenScalar E U) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (smoothOpenScalarExtend f) U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
  have he : (fun y : U => smoothOpenScalarExtend f y.val) = f.val := by
    funext y
    exact smoothOpenScalarExtend_apply f y y.property
  rw [he]
  exact f.property ⟨x, hx⟩

def supportedOverlapScalar {U V : Opens M} (p : M → ℂ)
    (f : SmoothOpenScalar E (U ⊓ V)) : V → ℂ := by
  classical
  exact fun x => if hx : x.val ∈ U then p x.val * f ⟨x.val, hx, x.property⟩ else 0

theorem supportedOverlapScalar_contMDiff {U V : Opens M} (p : M → ℂ)
    (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ p) (hs : tsupport p ⊆ U)
    (f : SmoothOpenScalar E (U ⊓ V)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (supportedOverlapScalar p f) := by
  let : ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ := by
    refine ⟨?_⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contDiff_mul.contMDiff
  intro x
  by_cases hx : x.val ∈ U
  · have hf := (smoothOpenScalarExtend_contMDiffOn f).contMDiffAt
      ((U ⊓ V).isOpen.mem_nhds ⟨hx, x.property⟩)
    have hg := hp.contMDiffAt.mul hf
    apply (hg.comp x (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffAt).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (U.isOpen.mem_nhds hx)] with y hy
    change y.val ∈ U at hy
    change supportedOverlapScalar p f y = p y.val * smoothOpenScalarExtend f y.val
    rw [supportedOverlapScalar, dite_eq_left hy, smoothOpenScalarExtend_apply f y.val ⟨hy, y.property⟩]
  · have hsupport : x.val ∉ tsupport p := fun h => hx (hs h)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
      (continuous_subtype_val.continuousAt : Tendsto (Subtype.val : V → M) (𝓝 x) (𝓝 x.val))
    apply (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change p y.val = 0 at hy
    unfold supportedOverlapScalar
    split_ifs
    · rw [hy, zero_mul]
    · rfl

end

/-! A finite smooth additive cocycle is an actual coboundary. The
primitive uses a subordinate partition and supported overlap extensions. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {ι : Type} [Fintype ι]

theorem exists_smooth_additive_cocycle_primitive (U : ι → Opens M)
    (hU : ∀ x : M, ∃ i, x ∈ U i)
    (g : ∀ i j, SmoothOpenScalar E (U i ⊓ U j))
    (hg : ∀ i j k (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k),
      g i j ⟨x, hi, hj⟩ + g j k ⟨x, hj, hk⟩ = g i k ⟨x, hi, hk⟩) :
    ∃ r : ∀ i, SmoothOpenScalar E (U i),
      ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
        r j ⟨x, hj⟩ - r i ⟨x, hi⟩ = g i j ⟨x, hi, hj⟩ := by
  classical
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ
    (fun i => (U i : Set M)) (fun i => (U i).isOpen) (fun x _ => mem_iUnion.mpr (hU x))
  let q := fun i x => (p i x : ℂ)
  have hq (i : ι) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (q i) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp (p i).contMDiff
  have hsupport (i : ι) : tsupport (q i) ⊆ U i := by
    have he : Function.support (q i) = Function.support (p i) := by
      ext x
      simp only [Function.mem_support, q, ne_eq, Complex.ofReal_eq_zero]
    change closure (Function.support (q i)) ⊆ U i
    rw [he]
    exact hp i
  have hsum (x : M) : ∑ i, q i x = 1 := by
    have H := p.sum_eq_one (mem_univ x)
    simpa only [finsum_eq_sum_of_fintype, q, ← Complex.ofReal_sum, Complex.ofReal_one] using
      congrArg (fun a : ℝ => (a : ℂ)) H
  let r : ∀ i, SmoothOpenScalar E (U i) := fun i =>
    ⟨fun x => ∑ k, supportedOverlapScalar (q k) (g k i) x,
      ContMDiff.sum (fun k _ => supportedOverlapScalar_contMDiff (q k) (hq k) (hsupport k) (g k i))⟩
  refine ⟨r, ?_⟩
  intro i j x hi hj
  change (∑ k, supportedOverlapScalar (q k) (g k j) ⟨x, hj⟩) -
    (∑ k, supportedOverlapScalar (q k) (g k i) ⟨x, hi⟩) = g i j ⟨x, hi, hj⟩
  rw [← Finset.sum_sub_distrib]
  have hterm (k : ι) :
      supportedOverlapScalar (q k) (g k j) ⟨x, hj⟩ -
        supportedOverlapScalar (q k) (g k i) ⟨x, hi⟩ = q k x * g i j ⟨x, hi, hj⟩ := by
    by_cases hx : x ∈ U k
    · simp only [supportedOverlapScalar, dite_eq_left hx]
      rw [← hg k i j x hx hi hj]
      ring
    · have hz : q k x = 0 := by
        by_contra h
        exact hx (hsupport k (subset_tsupport (q k) h))
      simp only [supportedOverlapScalar, dite_eq_right hx, sub_self, hz, zero_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, one_mul]

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothCocyclePrimitive
