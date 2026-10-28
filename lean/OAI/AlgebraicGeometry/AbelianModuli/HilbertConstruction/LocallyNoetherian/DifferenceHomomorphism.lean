import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.RelativeCube
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Difference Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.DifferenceHomomorphism.Theta.Geometric

noncomputable section

/-! The normalized difference family is a homomorphism on every test
scheme over a locally Noetherian projective base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupFunctor.Construction

variable {S : Scheme.{0}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem relative_groupDifferenceClass_comm (q : Line.Bundles.LineBundle.IsoClass A.scheme.left)
    {T : Over S} (a b : T ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme q a b = RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass A.scheme q b a := by
  unfold RepresentationTheory.Theta.Geometric.TestDifferenceClasses.groupDifferenceClass
  rw [mul_comm a b]
  exact mul_right_comm _ _ _

variable [IsLocallyNoetherian S] (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left)

include P

theorem locallyNoetherian_parameterDifferenceLineClass_mul
    {T : Over S} (a b : T ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) (a * b) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a *
        RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) b := by
  rw [Local.DifferenceHomogeneity.Theta.Geometric.local_difference_parameter_class, MonObj.comp_mul,
    relative_groupDifferenceClass_comm A _ _ (snd T A.scheme),
    RelativeCube.Theta.Geometric.locallyNoetherian_groupDifference_mul_right A P L,
    relative_groupDifferenceClass_comm A _ (snd T A.scheme),
    relative_groupDifferenceClass_comm A _ (snd T A.scheme)]
  rw [Local.DifferenceHomogeneity.Theta.Geometric.local_difference_parameter_class, Local.DifferenceHomogeneity.Theta.Geometric.local_difference_parameter_class]

theorem locallyNoetherian_parameterDifferenceHomogeneousClass_mul
    (hHom : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
    {T : Over S} (a b : T ⟶ A.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom (a * b) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom a *
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom b := by
  let φ := Picard.Homomorphisms.GroupSheafification.Construction.picardTypeSheafifyUnitHom (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A) (.op T)
  have hq : RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom (a * b) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom a *
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom b := by
    apply Subtype.ext
    exact locallyNoetherian_parameterDifferenceLineClass_mul A P L a b
  exact (congrArg φ hq).trans (φ.map_mul _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.DifferenceHomomorphism.Theta.Geometric
