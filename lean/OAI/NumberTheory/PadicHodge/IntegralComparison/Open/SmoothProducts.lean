import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.SmoothProduct
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham

/-! # Smooth Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothProducts

noncomputable section

/-! The genuine open-manifold product agrees with the intrinsic
manifold product under the derivative of the open inclusion. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (U : Opens M)

def wedge (p q : ℕ) : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (p + q) :=
  LinearMap.mk₂ ℂ AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge
    (fun x x' y => AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_add_left x x' y)
    (fun c x y => AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_smul_left c x y)
    (fun x y y' => AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_add_right x y y')
    (fun c x y => AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_smul_right c x y)

theorem intrinsic_wedge (p q : ℕ) (x : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p)
    (y : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q) (wedge U p q x y) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U p x) (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U q y) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro z
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_apply, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge_apply,
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_apply, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_apply]
  change (AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge x y z).compContinuousLinearMap _ = _
  rw [AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_apply]
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (E := E) (F := E) _ _ _).symm

theorem intrinsic_symm_wedge (p q : ℕ) (x : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U p)
    (y : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U q) :
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q)).symm (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge x y) =
      wedge U p q ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U p).symm x)
        ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U q).symm y) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q)).injective
  rw [LinearEquiv.apply_symm_apply, intrinsic_wedge,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem wedge_restrict {V : Opens M} (h : V ≤ U) (p q : ℕ)
    (x : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (y : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (wedge U p q x y) =
      wedge V p q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h x) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h y) :=
  AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_restrict h x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothProducts
