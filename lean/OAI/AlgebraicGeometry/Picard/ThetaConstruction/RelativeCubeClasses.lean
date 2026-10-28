import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle

/-! # Relative Cube Classes -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeCubeClasses.Geometric

noncomputable section

/-! The original Picard cube class over an arbitrary base and its
actual scheme base-change law. On every algebraically closed field it
is trivial by the proved geometric cube theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints

universe u
variable {S : Scheme.{u}} {X : Over S} [GrpObj X]

def relativeCubeClass (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left) {U : Over S} (a b c : U ⟶ X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left :=
  RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b * c).left q * RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q *
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback b.left q * RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback c.left q /
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * b).left q * RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (a * c).left q *
        RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (b * c).left q)

theorem relativeCubeClass_pullback (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left)
    {U V : Over S} (j : V ⟶ U) (a b c : U ⟶ X) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback j.left (relativeCubeClass q a b c) =
      relativeCubeClass q (j ≫ a) (j ≫ b) (j ≫ c) := by
  simp only [relativeCubeClass, map_div, map_mul, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
  have hm (x y : U ⟶ X) : j.left ≫ (x * y).left = ((j ≫ x) * (j ≫ y)).left :=
    congrArg Over.Hom.left (MonObj.comp_mul j x y)
  simp only [hm, Over.comp_left]
  rw [MonObj.comp_mul j a b]

omit [GrpObj X] in
theorem pointClass_baseChange (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left) {S' : Scheme.{u}}
    (f : S' ⟶ S) {U : Over S} (a : U ⟶ X) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst U.hom f)
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback a.left q) =
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback ((Over.pullback f).map a).left
      (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst X.hom f) q) := by
  rw [RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
  apply congrArg (fun v => RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback v q)
  simp only [Over.pullback_map_left, pullback.lift_fst]

local instance cubeBaseChangeGroup {S' : Scheme.{u}} (f : S' ⟶ S) :
    GrpObj ((Over.pullback f).obj X) := Functor.grpObjObj

theorem relativeCubeClass_baseChange (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left) {S' : Scheme.{u}}
    (f : S' ⟶ S) {U : Over S} (a b c : U ⟶ X) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst U.hom f) (relativeCubeClass q a b c) =
      relativeCubeClass (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (pullback.fst X.hom f) q)
        ((Over.pullback f).map a) ((Over.pullback f).map b) ((Over.pullback f).map c) := by
  simp only [relativeCubeClass, map_div, map_mul, pointClass_baseChange, Functor.map_mul]

theorem relativeCubeClass_eq_one_overField {K : Type u} [Field K] [IsAlgClosed K]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left)
    {U : Over (Spec (.of K))} (a b c : U ⟶ A.scheme) : relativeCubeClass q a b c = 1 := by
  let : GeometricallyIntegral A.scheme.hom :=
    FormalGeometry.Completion.SmoothGeometricIntegrality.Construction.proper_smooth_geometricallyIntegral_of_geometricallyConnected A.scheme.hom
  have h := FormalGeometry.Completion.CubeIdentity.Construction.cube_class_eq_one A.scheme q.out a b c
  have hd (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left) : Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dualClass r = r⁻¹ :=
    eq_inv_of_mul_eq_one_left (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.dual_tensorClass r)
  have he : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A.scheme q.out a b c =
      relativeCubeClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) a b c := by
    dsimp only [Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube, Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value,
      Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map, relativeCubeClass, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback]
    let numerator : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left :=
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a * b * c).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out)
    let denominator : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass U.left :=
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a * b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a * c).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (b * c).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out)
    exact congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass numerator) (hd denominator)
  have h' := he.symm.trans h
  have hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf q.out = q := Quotient.out_eq q
  exact (congrArg (fun r => relativeCubeClass r a b c) hq).symm.trans h'

theorem identityNormalizedLine_one_class {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (U : Over S) :
    RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (1 : U ⟶ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) = 1 := by
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.one_point_left, ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp]
  have h : RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback η[A.scheme].left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.identityNormalizedLine A L)) = 1 :=
    Quotient.sound (RelativeDifferenceBundle.Geometric.identityNormalizedLine_axis A L)
  rw [h, map_one]

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeCubeClasses.Geometric
