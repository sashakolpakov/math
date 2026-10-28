import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AmbientSchemeModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AmbientFlattenedIso

/-! # Projective Coefficient Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveCoefficientModel

noncomputable section

/-! A projective coefficient scheme with smooth recovery has a smooth projective closed model over one finitely generated noetherian coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_smooth_projective_coefficient_model
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    (X : Over (Spec (.of C))) [CompactSpace X.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom C.val.toRingHom))).obj X).hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) :
    ∃ (K : Subalgebra ℤ R) (hCK : C ≤ K), Algebra.FiniteType ℤ K ∧ IsNoetherianRing K ∧
      Nonempty (ProjectiveClosedModel.SmoothProjectiveClosedModel
        ((Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCK).toRingHom))).obj X)
        (SubalgebraRecoverySpec.subalgebraRecoverySpec (C := ℤ) (R := R) K)) := by
  obtain ⟨M, N, D, hD, ⟨L⟩⟩ := Projective.AmbientSchemeModels.exists_smooth_projective_ambient_scheme_model C X P
  have : Algebra.FiniteType ℤ M.coefficients := M.finiteType
  obtain ⟨hMD, hFT, hN⟩ := N.finalCoefficients_finiteType M.coefficients D hD
  let K := D.restrictScalars ℤ
  have hCK : C ≤ K := M.above.trans hMD
  let e := N.flattenedAmbientIso_above C M.coefficients M.above D hMD X
  refine ⟨K, hCK, hFT, hN, ?_⟩
  exact ⟨L.transport e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveCoefficientModel
