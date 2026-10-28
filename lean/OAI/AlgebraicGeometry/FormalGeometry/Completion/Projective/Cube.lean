import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCube
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricChowModification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected

/-! # Cube -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cube.Construction

noncomputable section

/-! The actual cube class vanishes after two pointed geometric Chow modifications.
No projectivity hypothesis is imposed on the original proper smooth group. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

omit [IsCommMonObj A] [Smooth A.hom] [GeometricallyIntegral A.hom] in
/-- The actual projective modification admits a rational lift of the group identity. -/
theorem chowModification_origin_lift
    [IsIntegral A.left] :
    ∃ s : Spec (CommRingCat.of K) ⟶ (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).scheme,
      s ≫ (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).projection = Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A := by
  have : IsProper (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).projection :=
    (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).proper
  have : Surjective (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).projection :=
    (Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom).surjective
  exact RationalPointLift.Construction.exists_rationalPoint_lift _ (Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A)

/-- The cube identity on the product of the actual two Chow modifications and the group. -/
theorem chowModification_cube_class_eq_one [IsIntegral A.left] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A (D.projection ≫ A.hom) (D.projection ≫ A.hom) D.projection rfl)
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A (D.projection ≫ A.hom) (D.projection ≫ A.hom) D.projection rfl)
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A (D.projection ≫ A.hom) (D.projection ≫ A.hom)) = 1 := by
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom
  have : IsProper D.projection := D.proper
  have : GeometricallyIntegral (D.projection ≫ A.hom) := D.geometricallyIntegral A.hom
  obtain ⟨s, hs⟩ := chowModification_origin_lift A
  have hsbase : s ≫ (D.projection ≫ A.hom) = 𝟙 _ := by
    rw [← Category.assoc, hs, Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin_over]
  exact Quotients.FiniteDescent.ProjectiveCube.Construction.ProjectiveCubeTriviality.class_eq_one A (D.projection ≫ A.hom)
    (D.projection ≫ A.hom) D.sectionCover D.sectionCover D.projection rfl D.projection rfl
    s hsbase hs s hsbase hs L

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cube.Construction
