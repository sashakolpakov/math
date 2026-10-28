import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCube
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCubicalFaces
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantSectionCoverPoint
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialityFromBaseChange

/-! # Pointed Constant Product Cube -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedConstantProductCube.Construction

noncomputable section

/-! The cubical defect vanishes after pullback to any two pointed projective factors over the group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem pointed_constantProduct_cube_trivial
    {K : Type} [Field K] [IsAlgClosed K]
    (A B G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
    [IsProper A.hom] [IsProper B.hom] [IsProper G.hom]
    [GeometricallyIntegral A.hom] [GeometricallyIntegral B.hom] [IsIntegral G.left]
    (DA : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data A.left) (DB : AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data B.left)
    (a : A ⟶ G) (b : B ⟶ G)
    (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) (ha : sA ≫ a = η[G])
    (sB : 𝟙_ (Over (Spec (.of K))) ⟶ B) (hb : sB ≫ b = η[G]) (l : PicardEq.Construction.Picard G.left) :
    Nonempty ((ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A B G a b l).sheaf ≅
      LineBundle.Construction.structureSheafModule (ConstantProductCoordinates.Construction.constantProduct A B G).left) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : A.left.IsSeparated := by constructor; rw [← terminal.comp_from A.hom]; infer_instance
  have : B.left.IsSeparated := by constructor; rw [← terminal.comp_from B.hom]; infer_instance
  have : IsProper (A ⊗ G).hom := inferInstanceAs (IsProper (pullback.fst A.hom G.hom ≫ A.hom))
  have : IsProper (B ⊗ G).hom := inferInstanceAs (IsProper (pullback.fst B.hom G.hom ≫ B.hom))
  have : (A ⊗ G).left.IsSeparated := by constructor; rw [← terminal.comp_from (A ⊗ G).hom]; infer_instance
  have : (B ⊗ G).left.IsSeparated := by constructor; rw [← terminal.comp_from (B ⊗ G).hom]; infer_instance
  let f := ConstantProductCoordinates.Construction.constantLeftBase A G
  let g := ConstantProductCoordinates.Construction.constantRightBase B G
  let p := (fst A G).left
  let q := (fst B G).left
  let hp := IsPullback.of_hasPullback A.hom G.hom
  let hq := IsPullback.of_hasPullback B.hom G.hom
  have : IsProper f := inferInstanceAs (IsProper (pullback.snd A.hom G.hom))
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd B.hom G.hom))
  have : Flat f := inferInstanceAs (Flat (pullback.snd A.hom G.hom))
  have : Flat g := inferInstanceAs (Flat (pullback.snd B.hom G.hom))
  have : GeometricallyIntegral f := inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom G.hom))
  have : GeometricallyIntegral g := inferInstanceAs (GeometricallyIntegral (pullback.snd B.hom G.hom))
  let sX := (ConstantProductCoordinates.Construction.constantFamilySection A G sA).left
  let sY := (ConstantProductCoordinates.Construction.constantFamilySection B G sB).left
  have hsX : sX ≫ f = 𝟙 _ := congrArg Over.Hom.left (ConstantProductCoordinates.Construction.constantFamilySection_base A G sA)
  have hsY : sY ≫ g = 𝟙 _ := congrArg Over.Hom.left (ConstantProductCoordinates.Construction.constantFamilySection_base B G sB)
  let L := ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A B G a b l
  obtain ⟨eX⟩ := ConstantProductCubicalFaces.Construction.constantProductCubicalBundle_left_trivial A B G a b l sB hb
  obtain ⟨eY⟩ := ConstantProductCubicalFaces.Construction.constantProductCubicalBundle_right_trivial A B G a b l sA ha
  obtain ⟨i₀, hi₀⟩ := ConstantSectionCoverPoint.Construction.exists_constantSection_cover_index A G DA sA
  obtain ⟨j₀, hj₀⟩ := ConstantSectionCoverPoint.Construction.exists_constantSection_cover_index B G DB sB
  let π := ConstantProductCoordinates.Construction.constantProductProjection A B G
  let u := (η[G]).left
  have hu : u ≫ G.hom = 𝟙 _ := Over.w η[G]
  have : IsClosedImmersion (u ≫ G.hom) := hu.symm ▸ (inferInstance : IsClosedImmersion (𝟙 _))
  have : IsClosedImmersion u := IsClosedImmersion.of_comp u G.hom
  let j := (ConstantProductPointFiber.Construction.constantProductPointFiber A B G η[G]).left
  have hj : IsPullback j (A ⊗ B).hom π u := ConstantProductPointFiber.Construction.constantProductPointFiberMap_isPullback A B G η[G]
  obtain ⟨ej⟩ := ConstantProductCubicalFaces.Construction.constantProductCubicalBundle_unit_trivial A B G a b l
  let eu := CartesianTrivializationComparison.Construction.cartesianTrivialization_to_native j π (A ⊗ B).hom u hj L.sheaf ej
  let x := IsLocalRing.closedPoint K
  let e₀ := TrivialityFromBaseChange.Construction.lineBundleFiberTrivialization_of_baseChange π u L.sheaf x eu
  exact ConstantProductCube.Construction.constantProduct_lineBundle_trivial A.hom B.hom f g p q G.hom hp hq DA DB
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L.sheaf L.isLineBundle eX eY (u x) ⟨e₀⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedConstantProductCube.Construction
