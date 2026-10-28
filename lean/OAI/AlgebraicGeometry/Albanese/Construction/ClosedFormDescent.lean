import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import Mathlib.Topology.Constructions

/-! # Closed Form Descent -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.ClosedFormDescent

noncomputable section

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

/-- Local constancy descends along any quotient map. -/
theorem locallyConstant_of_quotient_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Topology.IsQuotientMap f) (g : Y → Z)
    (hg : IsLocallyConstant (g ∘ f)) : IsLocallyConstant g :=
  fun s => hf.isCoinducing.isOpen_preimage.mp (hg s)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A global smooth zero-form with zero exterior derivative has a locally
constant scalar function, without a compactness assumption. -/
theorem zeroFormScalar_locallyConstant_of_d_zero (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hform : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0) :
    IsLocallyConstant (ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar form) := by
  have h := (Analysis.DifferentialForms.Manifold.LocallyConstant.d_openManifoldZeroForm_eq_zero_iff (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form)).mp (by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, hform, map_zero])
  exact h.comp_continuous (continuous_id.subtype_mk (fun _ => trivial))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Pullback of zero-forms is ordinary composition of their scalar functions. -/
theorem zeroFormScalar_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N 0) :
    ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form) =
      ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar form ∘ f := by
  funext x
  change form (f x) _ = form (f x) 0
  congr 1
  exact Subsingleton.elim _ _

/-- Closed one-forms are detected by smooth quotient maps. A local primitive
pulls back to a locally constant function, which descends through the quotient. -/
theorem closed_oneForm_eq_zero_of_quotient_pullback [FiniteDimensional ℝ F]
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hq : Topology.IsQuotientMap f) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms F N 1)
    (hzero : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form.val = 0) : form = 0 := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro y
  obtain ⟨U, hy, primitive, hp⟩ := ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.exists_local_intrinsic_primitive form y
  let V : Opens M := ⟨f ⁻¹' (U : Set N), U.isOpen.preimage hf.continuous⟩
  let g : V → U := fun x => ⟨f x, x.property⟩
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact hf.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))
  have hqg : Topology.IsQuotientMap g := hq.restrictPreimage_isOpen U.isOpen
  have hdp : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg primitive) = 0 := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, hp]
    have hcomp : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.restrictSmoothForm U 1 form.val) =
        ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.restrictSmoothForm V 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form.val) := by
      unfold ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.restrictSmoothForm
      rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp, ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
      rfl
    rw [hcomp, hzero, map_zero]
  have hloc := zeroFormScalar_locallyConstant_of_d_zero _ hdp
  rw [zeroFormScalar_pullback] at hloc
  have hpzero : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = 0 :=
    ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.d_zeroForm_eq_zero_of_locallyConstant primitive
      (locallyConstant_of_quotient_comp g hqg _ hloc)
  have hrest : ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.restrictSmoothForm U 1 form.val = 0 := hp.symm.trans hpzero
  have hopen : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form.val = 0 := by
    apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv F U 1).injective
    rw [map_zero, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]
    exact hrest
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm F U 1 => a ⟨y, hy⟩) hopen

end

end OAI.AlgebraicGeometry.Albanese.Construction.ClosedFormDescent
