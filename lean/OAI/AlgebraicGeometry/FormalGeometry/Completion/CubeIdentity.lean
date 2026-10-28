import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cube
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeModification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ChowModificationFunctions

/-! # Cube Identity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity

noncomputable section

/-! The actual geometric cube identity descends to the original proper
smooth group, without assuming that this group is projective. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem universal_cube_class_eq_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A A.hom A.hom (𝟙 A.left) (Category.id_comp _))
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A A.hom A.hom (𝟙 A.left) (Category.id_comp _))
      (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A A.hom A.hom) = 1 := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let D := Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build A.hom
  have : IsProper D.projection := D.proper
  have hnormal (x : A.left) : IsIntegrallyClosed (A.left.presheaf.stalk x) := by
    have := Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk A.hom x
    infer_instance
  have hsections (U : A.left.Opens) : IsIso (D.projection.app U) :=
    ChowModificationFunctions.Construction.chowModification_app_isIso A.hom hnormal U
  apply CubeModification.Construction.cubeModification_picard_injective A D.projection D.projection hsections hsections
  rw [map_one, Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.pullback, CubeModification.Construction.cubeModification_first,
    CubeModification.Construction.cubeModification_second, CubeModification.Construction.cubeModification_third]
  exact Projective.Cube.Construction.chowModification_cube_class_eq_one A L

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [GrpObj A] [IsCommMonObj A] in
def cubeCoordinateLift {T : Over (Spec (CommRingCat.of K))} (a b c : T ⟶ A) :
    T ⟶ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.ambient A A.hom A.hom :=
  Over.homMk (pullback.lift
    (pullback.lift a.left c.left (a.w.trans c.w.symm))
    (pullback.lift b.left c.left (b.w.trans c.w.symm)) (by simp)) (by
      simp [Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.projection, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase, c.w])

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [GrpObj A] [IsCommMonObj A] in
theorem cubeCoordinateLift_first {T : Over (Spec (CommRingCat.of K))} (a b c : T ⟶ A) :
    cubeCoordinateLift A a b c ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A A.hom A.hom (𝟙 A.left) (Category.id_comp _) = a := by
  apply Over.OverMorphism.ext
  simp [cubeCoordinateLift, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first]

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [GrpObj A] [IsCommMonObj A] in
theorem cubeCoordinateLift_second {T : Over (Spec (CommRingCat.of K))} (a b c : T ⟶ A) :
    cubeCoordinateLift A a b c ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A A.hom A.hom (𝟙 A.left) (Category.id_comp _) = b := by
  apply Over.OverMorphism.ext
  simp [cubeCoordinateLift, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second]

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [GrpObj A] [IsCommMonObj A] in
theorem cubeCoordinateLift_third {T : Over (Spec (CommRingCat.of K))} (a b c : T ⟶ A) :
    cubeCoordinateLift A a b c ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A A.hom A.hom = c := by
  apply Over.OverMorphism.ext
  simp [cubeCoordinateLift, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.projection, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase]

/-- The geometric cube identity holds for maps from every actual scheme over the field. -/
theorem cube_class_eq_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a b c : T ⟶ A) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L a b c = 1 := by
  have h := congrArg (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (cubeCoordinateLift A a b c).left)
    (universal_cube_class_eq_one A L)
  simpa only [map_one, Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.pullback, cubeCoordinateLift_first,
    cubeCoordinateLift_second, cubeCoordinateLift_third] using h

theorem lineBundle_isCubical (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.IsCubical A L :=
  Quotients.FiniteDescent.CubePicardFaces.Construction.CubePicardClass.isCubical A L (cube_class_eq_one A L)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity
