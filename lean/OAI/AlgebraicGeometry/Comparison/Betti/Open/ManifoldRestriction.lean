import OAI.Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence

/-! # Manifold Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldRestriction.Holomorphic

noncomputable section

/-! Naturality of the actual coefficient-form equivalence under open restriction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U V : Opens E} {n : ℕ}

theorem smoothOpenManifoldEquiv_restrict (h : U ≤ V) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) :
    Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h)
        (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv V n form) := by
  let a := (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv V n).symm form
  have ha : Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv V n a = form :=
    (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv V n).apply_symm_apply form
  have hu : Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n
      (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a)) =
      Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
    exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).apply_symm_apply _
  have hv : Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V n a = Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv V n form := by
    rw [← ha]
    exact ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv V n).apply_symm_apply _).symm
  rw [Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_restrict, ha, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, hv] at hu
  exact hu

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldRestriction.Holomorphic
