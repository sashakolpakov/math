import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelFlattenedAmbientIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraPullbackComposition

/-! # Ambient Flattened Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An initial coefficient inclusion and the closed model stages combine into one direct base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel.flattenedAmbientIso_above
    {R : Type u} [CommRing R] (C C₁ : Subalgebra ℤ R) (hCC₁ : C ≤ C₁)
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C₁}
    (N : Closed.AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) (D : Subalgebra N.closingCoefficients R)
    (hMD : C₁ ≤ D.restrictScalars ℤ) (X : Over (Spec (.of C))) :=
  letI : CommRing N.coefficients := Subalgebra.toCommRing (R := C₁) (A := R) N.coefficients
  letI : CommRing N.closingCoefficients :=
    Subalgebra.toCommRing (R := N.coefficients) (A := R) N.closingCoefficients
  letI : CommRing D := Subalgebra.toCommRing (R := N.closingCoefficients) (A := R) D
  N.flattenedAmbientIso C₁ D hMD
      ((Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCC₁).toRingHom))).obj X) ≪≫
    SubalgebraPullbackComposition.subalgebraPullbackCompIso (R := R) (A := N.closingCoefficients) C C₁ hCC₁ D hMD X

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
