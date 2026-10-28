import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FiniteLocalPrimitives
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant

/-! # Primitive Transitions -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PrimitiveTransitions.CM.Construction

noncomputable section

/-! Differences of actual local primitives are locally constant. Their
values on compact subsets of overlaps form finite sets. -/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def localFormRestriction {U V : Opens M} (hUV : U ≤ V) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U n :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : U => (⟨x.val, hUV x.property⟩ : V)) (by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))

theorem localFormRestriction_d {U V : Opens M} (hUV : U ≤ V) (n : ℕ)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (localFormRestriction hUV n f) =
      localFormRestriction hUV (n + 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback _ _ f

theorem localFormRestriction_global {U V : Opens M} (hUV : U ≤ V) (n : ℕ)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    localFormRestriction hUV n (Intersection.CM.Construction.restrictSmoothForm V n f) = Intersection.CM.Construction.restrictSmoothForm U n f := by
  unfold localFormRestriction Intersection.CM.Construction.restrictSmoothForm
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  rfl

theorem localFormRestriction_scalar {U V : Opens M} (hUV : U ≤ V)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0) (x : U) :
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (localFormRestriction hUV 0 f) x =
      HolomorphicPrimitive.CM.Construction.zeroFormScalar f ⟨x.val, hUV x.property⟩ := by
  change f _ _ = f _ 0
  congr 1
  exact Subsingleton.elim _ _

theorem localPrimitive_difference_closed {U V : Opens M}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm U 1 a)
    (hg : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm V 1 a) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      (localFormRestriction (show U ⊓ V ≤ U from inf_le_left) 0 f -
        localFormRestriction (show U ⊓ V ≤ V from inf_le_right) 0 g) = 0 := by
  rw [map_sub, localFormRestriction_d, localFormRestriction_d, hf, hg,
    localFormRestriction_global, localFormRestriction_global, sub_self]

theorem local_zeroForm_scalar_locallyConstant (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0) : IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) := by
  have h := (Analysis.DifferentialForms.Manifold.LocallyConstant.d_openManifoldZeroForm_eq_zero_iff (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ f)).mp (by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, hf, map_zero])
  exact h.comp_continuous (continuous_id.subtype_mk (fun _ => trivial))

def primitiveTransition {U V : Opens M}
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0) :
    (U ⊓ V : Opens M) → ℂ :=
  fun x => HolomorphicPrimitive.CM.Construction.zeroFormScalar f ⟨x.val, x.property.1⟩ -
    HolomorphicPrimitive.CM.Construction.zeroFormScalar g ⟨x.val, x.property.2⟩

theorem primitiveTransition_locallyConstant {U V : Opens M}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm U 1 a)
    (hg : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm V 1 a) :
    IsLocallyConstant (primitiveTransition f g) := by
  let q : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (U ⊓ V : Opens M) 0 :=
    localFormRestriction (show U ⊓ V ≤ U from inf_le_left) 0 f -
    localFormRestriction (show U ⊓ V ≤ V from inf_le_right) 0 g
  have hscalar : IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar q) :=
    local_zeroForm_scalar_locallyConstant q (localPrimitive_difference_closed a f g hf hg)
  have heq : HolomorphicPrimitive.CM.Construction.zeroFormScalar q = primitiveTransition f g := by
    funext x
    change HolomorphicPrimitive.CM.Construction.zeroFormScalar (localFormRestriction _ 0 f) x -
      HolomorphicPrimitive.CM.Construction.zeroFormScalar (localFormRestriction _ 0 g) x = _
    rw [localFormRestriction_scalar, localFormRestriction_scalar]
    rfl
  rwa [heq] at hscalar

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem primitiveTransition_cocycle {U V W : Opens M}
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (h : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E W 0) (x : M) (hxU : x ∈ U) (hxV : x ∈ V) (hxW : x ∈ W) :
    primitiveTransition f g ⟨x, hxU, hxV⟩ + primitiveTransition g h ⟨x, hxV, hxW⟩ =
      primitiveTransition f h ⟨x, hxU, hxW⟩ := by
  unfold primitiveTransition
  ring

theorem primitiveTransition_compact_range {U V : Opens M}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm U 1 a)
    (hg : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm V 1 a)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U) (hKV : K ⊆ V) :
    (Set.range (fun x : K => primitiveTransition f g
      ⟨x.val, hKU x.property, hKV x.property⟩)).Finite := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact ((primitiveTransition_locallyConstant a f g hf hg).comp_continuous
    (continuous_subtype_val.subtype_mk (fun x => ⟨hKU x.property, hKV x.property⟩))).range_finite

theorem finite_coordinate_locallyConstant {X ι Y : Type*} [TopologicalSpace X] [Finite ι]
    (f : X → ι → Y) (hf : ∀ i, IsLocallyConstant (fun x => f x i)) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  exact (Filter.eventually_all.mpr (fun i => (hf i).eventually_eq x)).mono
    (fun _ h => funext h)

theorem primitiveTransition_family_compact_range {U V : Opens M}
    {ι : Type*} [Finite ι] (a : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) = Intersection.CM.Construction.restrictSmoothForm U 1 (a i))
    (hg : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (g i) = Intersection.CM.Construction.restrictSmoothForm V 1 (a i))
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U) (hKV : K ⊆ V) :
    (Set.range (fun x : K => fun i => primitiveTransition (f i) (g i)
      ⟨x.val, hKU x.property, hKV x.property⟩)).Finite := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply IsLocallyConstant.range_finite
  apply finite_coordinate_locallyConstant
  intro i
  exact (primitiveTransition_locallyConstant (a i) (f i) (g i) (hf i) (hg i)).comp_continuous
    (continuous_subtype_val.subtype_mk (fun x => ⟨hKU x.property, hKV x.property⟩))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PrimitiveTransitions.CM.Construction
