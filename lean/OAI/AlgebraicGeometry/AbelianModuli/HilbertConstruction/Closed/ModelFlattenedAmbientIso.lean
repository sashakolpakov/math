import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ModelAmbientBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraBaseInclusion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleOverPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TripleSpectrumComposition

/-! # Model Flattened Ambient Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! The three ambient coefficient stages agree with direct base change to the final coefficient subalgebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def AlgebraDiagramModel.ClosedAlgebraDiagramModel.flattenedAmbientIso
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R)
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C}
    (M : AlgebraDiagramModel.ClosedAlgebraDiagramModel (R := R) A B) (D : Subalgebra M.closingCoefficients R)
    (hCD : C ≤ D.restrictScalars ℤ) (X : Over (Spec (.of C))) :
    M.ambientBaseChange D X ≅
      (Over.pullback (SubalgebraBaseInclusion.subalgebraBaseInclusionSpec (A := M.closingCoefficients) C D hCD)).obj X := by
  letI : CommRing D := Subalgebra.toCommRing (R := M.closingCoefficients) (A := R) D
  let f : CommRingCat.of C ⟶ CommRingCat.of M.coefficients := CommRingCat.ofHom (algebraMap C M.coefficients)
  let g : CommRingCat.of M.coefficients ⟶ CommRingCat.of M.closingCoefficients :=
    CommRingCat.ofHom (algebraMap M.coefficients M.closingCoefficients)
  let h : CommRingCat.of M.closingCoefficients ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (algebraMap M.closingCoefficients D)
  let k : CommRingCat.of C ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (SubalgebraBaseInclusion.subalgebraBaseInclusion (A := M.closingCoefficients) (R := R) C D hCD)
  have hk : f ≫ g ≫ h = k := by
    ext x
    rfl
  exact TripleOverPullbackIso.tripleOverPullbackIso (Spec.map f) (Spec.map g) (Spec.map h) (Spec.map k)
    (TripleSpectrumComposition.tripleSpectrumComposition f g h k hk) X

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
