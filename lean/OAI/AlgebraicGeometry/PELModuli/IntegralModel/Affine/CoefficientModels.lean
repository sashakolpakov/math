import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models

/-! # Coefficient Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.CoefficientModels.Coefficients

noncomputable section

/-! Finite coefficient models of affine schemes retain actual affineness
of the model, in addition to their generic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem affine_has_affine_coefficient_model
    (A : Type) [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] :
    ∃ M : Coefficient.Models.Coefficients.CoefficientModel R K (ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver K A), IsAffine M.model.left := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K A
  let s : Finset K := P.finite_coeffs.toFinset
  let L := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  let : P.HasCoeffs L := ⟨fun c hc => ⟨⟨c, Algebra.subset_adjoin (by simpa [s] using hc)⟩, rfl⟩⟩
  let A₀ := P.ModelOfHasCoeffs L
  refine ⟨{
    coefficients := s
    model := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver L A₀
    finitePresentation := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver_finitePresentation L A₀
    genericIso := ArithmeticGeometry.Models.Scheme.Constructions.Foundations.baseChangeAffineIso L K A₀ ≪≫ ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOverIso (P.tensorModelOfHasCoeffsEquiv L)
  }, ?_⟩
  exact inferInstanceAs (IsAffine (Spec (.of A₀)))

theorem isAffine_has_affine_coefficient_model
    (X : Over (Spec (.of K))) [IsAffine X.left]
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    ∃ M : Coefficient.Models.Coefficients.CoefficientModel R K X, IsAffine M.model.left := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let A := Γ(X.left, ⊤)
  let : Algebra K A := φ.hom.toAlgebra
  have hφFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Algebra.FinitePresentation K A := (LocallyOfFinitePresentation.SpecMap_iff φ).mp hφFP
  obtain ⟨M, hM⟩ := affine_has_affine_coefficient_model (R := R) (K := K) A
  let e : X ≅ ArithmeticGeometry.Models.Scheme.Constructions.Foundations.affineOver K A := Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.map φ = X.hom
    rw [hφ, Iso.hom_inv_id_assoc])
  exact ⟨M.transport e.symm, hM⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.CoefficientModels.Coefficients
