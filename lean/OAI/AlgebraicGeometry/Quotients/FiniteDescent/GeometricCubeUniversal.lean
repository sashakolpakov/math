import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCube
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLeft
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRight
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperRational

/-! # Geometric Cube Universal -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeUniversal

noncomputable section

/-! The geometric cube class vanishes on the original proper smooth
commutative group. Projective modifications supply the two factors for
seesaw, and flat base change gives faithful Picard descent. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.GeometricCubeClass

variable {K : Type u} [Field K] [IsAlgClosed K] (A : Over (Spec (.of K)))
variable [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]

 theorem universal_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    CubePicardValue.Construction.CubePicardClass.cube A L
      (CubeProductBase.Construction.CubeProductCoordinates.first A A.hom A.hom (𝟙 A.left) (Category.id_comp _))
      (CubeProductBase.Construction.CubeProductCoordinates.second A A.hom A.hom (𝟙 A.left) (Category.id_comp _)) (CubeProductBase.Construction.CubeProductCoordinates.third A A.hom A.hom) = 1 := by
  have : GeometricallyIntegral A.hom := AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral A
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let D := ChowModificationModel.Construction.ChowModification.build A.hom
  let q := D.projection
  have : IsIntegral D.scheme := D.integral
  have : IsProper q := D.proper
  have : Surjective q := D.surjective
  have : IsProper (q ≫ A.hom) := inferInstance
  have : GeometricallyIntegral (q ≫ A.hom) := D.geometricallyIntegral A.hom
  have : IsLocallyNoetherian D.scheme := LocallyOfFiniteType.isLocallyNoetherian (q ≫ A.hom)
  have : CompactSpace D.scheme := QuasiCompact.compactSpace_of_compactSpace (q ≫ A.hom)
  have : IsNoetherian D.scheme := ⟨⟩
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (q ∣_ D.cover.common) := D.isIso_restrict
  have hq (U : A.left.Opens) : IsIso (q.app U) :=
    ProperModification.Construction.ProperModificationFunctions.smooth_isIso_app q D.cover.common A.hom U
  obtain ⟨s, hs⟩ := ProperRational.Construction.ProperRationalLift.exists_lift q (CubeProductFrames.Construction.CubeProductCoordinates.origin A)
  have hsbase : s ≫ (q ≫ A.hom) = 𝟙 _ := by
    rw [← Category.assoc, hs, CubeProductFrames.Construction.CubeProductCoordinates.origin_over]
  have hc := ProjectiveCube.Construction.ProjectiveCubeTriviality.class_eq_one A (q ≫ A.hom) (q ≫ A.hom)
    D.sectionCover D.sectionCover q rfl q rfl s hsbase hs s hsbase hs L
  apply CubeLeft.Construction.CubeLeftFactorMap.picard_injective A A.hom A.hom q hq
  rw [map_one, CubeLeft.Construction.CubeLeftFactorMap.cube]
  simp only [Category.comp_id]
  apply CubeRight.Construction.CubeRightFactorMap.picard_injective A (q ≫ A.hom) A.hom q hq
  rw [map_one, CubeRight.Construction.CubeRightFactorMap.cube]
  simpa only [Category.comp_id] using hc

end Construction.GeometricCubeClass

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeUniversal
