import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness
import OAI.RepresentationTheory.Theta.Geometric.Projective.BaseChange

/-! # Coefficient Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels.Coefficients

noncomputable section

/-! Standard projective spaces have actual finite coefficient models.
The generic comparison is the proved projective-space base-change square,
and properness and finite presentation hold over the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def affineProjectiveBaseChangeIso {R K : Type} [CommRing R] [CommRing K]
    (f : R →+* K) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  Over.isoMk (RepresentationTheory.Theta.Geometric.Projective.BaseChange.RelativeProjective.projectiveBaseChangeIso f n)
    (RepresentationTheory.Theta.Geometric.Projective.BaseChange.RelativeProjective.coefficient_isPullback f n).isoPullback_hom_snd

variable (R K : Type) [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]

def projectiveCoefficientModel (n : ℕ) (s : Finset K) :
    Coefficient.Models.Coefficients.CoefficientModel R K (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n) := by
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s) := Coefficient.Finiteness.Coefficients.coefficientBase_locallyNoetherian R K s
  exact {
    coefficients := s
    model := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) n
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := (affineProjectiveBaseChangeIso (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s).val.toRingHom n).symm }

theorem projectiveCoefficientModel_proper (n : ℕ) (s : Finset K) :
    IsProper (projectiveCoefficientModel R K n s).model.hom :=
  AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace_proper (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) n

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels.Coefficients
