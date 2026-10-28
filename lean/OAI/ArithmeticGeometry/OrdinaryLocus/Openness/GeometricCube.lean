import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPicardDescent
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedConstantProductCube
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperPointLifting
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardModificationDescent
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricChowModification
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection

/-! # Geometric Cube -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricCube.Construction

noncomputable section

section

/-! The cube identity for a smooth proper geometrically connected commutative group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
variable [Smooth G.hom] [IsProper G.hom] [GeometricallyConnected G.hom]

theorem tripleCubeBundle_trivial (l : PicardEq.Construction.Picard G.left) :
    Nonempty ((TripleCube.Construction.tripleCubeBundle G l).sheaf ≅ LineBundle.Construction.structureSheafModule (TripleCube.Construction.cubeDomain G).left) := by
  have : GeometricallyIntegral G.hom := AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  let D := AlgebraicGeometry.Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification.build G.hom
  let A := Over.mk (D.projection ≫ G.hom)
  let q : A ⟶ G := Over.homMk D.projection
  have : IsIntegral A.left := D.integral
  have : IsProper q.left := D.proper
  have : Surjective q.left := D.surjective
  have : IsProper D.projection := D.proper
  have : IsProper A.hom := inferInstanceAs (IsProper (D.projection ≫ G.hom))
  have : GeometricallyIntegral A.hom := D.geometricallyIntegral G.hom
  have : Nonempty D.cover.common := D.cover.common_nonempty
  have : IsIso (q.left ∣_ D.cover.common) := D.isIso_restrict
  have hq (U : G.left.Opens) : IsIso (q.left.app U) :=
    AlgebraicGeometry.Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions.smooth_isIso_app q.left D.cover.common G.hom U
  obtain ⟨s, hs⟩ := ProperPointLifting.Construction.exists_point_lift_of_proper_surjective q η[G]
  have he := PointedConstantProductCube.Construction.pointed_constantProduct_cube_trivial A A G D.sectionCover D.sectionCover
    q q s hs s hs l
  have hz : PicardEq.Construction.lineBundleClass (ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A A G q q l).sheaf
      (ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A A G q q l).isLineBundle = 0 :=
    (PicardEq.Construction.lineBundleClass_eq_iff _ (LineBundle.Construction.isLineBundle_structureSheaf _)).mpr he
  have hi := ConstantProductPicardDescent.Construction.picardPullback_constantProductToTriple_injective A A G q q hq hq
  apply (PicardEq.Construction.lineBundleClass_eq_iff (TripleCube.Construction.tripleCubeBundle G l).isLineBundle
    (LineBundle.Construction.isLineBundle_structureSheaf _)).mp
  apply hi
  rw [PicardEq.Construction.lineBundleClass_unit, map_zero, ConstantProductToTriple.Construction.constantProductToTriple_cube_class]
  exact hz

theorem endomorphismPicardClass_isCubical (l : PicardEq.Construction.Picard G.left) :
    CubicalAlgebra.Construction.IsCubical (PicardMultiplication.Construction.endomorphismPicardClass G l) :=
  TripleCube.Construction.endomorphismPicardClass_isCubical_of_tripleCube_trivial G l (tripleCubeBundle_trivial G l)

theorem picardMultiplication (l : PicardEq.Construction.Picard G.left)
    (hs : PicardPullback.Construction.picardPullback ((𝟙 G : G ⟶ G)⁻¹).left l = l) (n : ℕ) :
    PicardPullback.Construction.picardPullback (Multiplication.Construction.multiplicationMap G n).left l = n ^ 2 • l :=
  PicardMultiplication.Construction.picardMultiplication_of_cubical G l (endomorphismPicardClass_isCubical G l) hs n

theorem symmetricLineBundleMultiplication (M : G.left.Modules) (hM : LineBundle.Construction.IsLineBundle M)
    (hs : Nonempty ((Scheme.Modules.pullback ((𝟙 G : G ⟶ G)⁻¹).left).obj M ≅ M)) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (Multiplication.Construction.multiplicationMap G n).left).obj M ≅
      TensorRestriction.Construction.sheafTensorPower M (n ^ 2)) :=
  PicardMultiplication.Construction.symmetricLineBundleMultiplication_of_cubical G M hM
    (endomorphismPicardClass_isCubical G (PicardEq.Construction.lineBundleClass M hM)) hs n

end

/-! Opposite translates of a line bundle tensor to its square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem picardTranslation_square (l : PicardEq.Construction.Picard A.left)
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    PicardPullback.Construction.picardPullback (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom l +
      PicardPullback.Construction.picardPullback (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom l = l + l := by
  let b : A ⟶ A := toUnit A ≫ a
  have hb : PicardPullback.Construction.picardPullback b.left l = 0 := PicardField.Construction.picardPullback_constant A.hom a.left l
  have hbi : PicardPullback.Construction.picardPullback b⁻¹.left l = 0 := by
    have he : b⁻¹ = toUnit A ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
    rw [he]
    exact PicardField.Construction.picardPullback_constant A.hom a⁻¹.left l
  have h := TripleCube.Construction.picardCubicalDefect_zero_of_tripleCube_trivial A l (tripleCubeBundle_trivial A l)
    (𝟙 A) b b⁻¹
  dsimp only [PicardCubicalDefect.Construction.picardCubicalDefect] at h
  simp only [mul_inv_cancel_right, mul_inv_cancel, hb, hbi, PicardCubicalDefect.Construction.picardPullback_one,
    show (𝟙 A : A ⟶ A).left = 𝟙 A.left from rfl, PicardPullback.Construction.picardPullback_id,
    AddMonoidHom.id_apply, add_zero, sub_zero] at h
  change PicardPullback.Construction.picardPullback (𝟙 A * b).left l +
    PicardPullback.Construction.picardPullback (𝟙 A * (toUnit A ≫ a⁻¹)).left l = l + l
  rw [GrpObj.comp_inv]
  exact (sub_eq_zero.mp (by simpa only [sub_sub] using h)).symm

theorem lineBundleTranslation_square (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    Nonempty (((L.pullback (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom).tensor
      (L.pullback (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom)).sheaf ≅
        (L.tensor L).sheaf) := by
  apply (PicardEq.Construction.lineBundleClass_eq_iff
    (TensorRestriction.Construction.isLineBundle_sheafTensor
      (LineBundle.Construction.isLineBundle_pullback _ L.sheaf L.locallyTrivial)
      (LineBundle.Construction.isLineBundle_pullback _ L.sheaf L.locallyTrivial))
    (TensorRestriction.Construction.isLineBundle_sheafTensor L.locallyTrivial L.locallyTrivial)).mp
  exact picardTranslation_square A (PicardEq.Construction.lineBundleClass L.sheaf L.locallyTrivial) a

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GeometricCube.Construction
