import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardBaseChange

/-! # Pair Poincare Class -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClass

noncomputable section

/-! The homogeneous sheaf class of a concrete line on an abelian pair,
and its exact restriction through scalar base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {S T : Scheme.{u}} {g : ℕ} (A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.scheme ⊗ A.scheme).left)
    (h : A.IsHomogeneousPicardClass D.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))

def pairPoincareClass : A.homogeneousPicardSheaf.obj.obj (.op D.scheme) :=
  (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op D.scheme)
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L, h⟩

theorem baseChangeProjection_eq_counit (b : T ⟶ S) :
    AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b = (Over.mapPullbackAdj b).counit.app D.scheme := by
  change ((Over.mapPullbackAdj b).homEquiv _ _).symm (𝟙 _) = _
  rw [(Over.mapPullbackAdj b).homEquiv_counit, (Over.map b).map_id, Category.id_comp]

theorem pairPoincareClass_baseChange (b : T ⟶ S)
    (h' : (A.pullback b).IsHomogeneousPicardClass (D.pullback b).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme)))) :
    A.homogeneousPicardBaseChangeEquiv b (D.pullback b).scheme
      (pairPoincareClass (A.pullback b) (D.pullback b)
        (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme)) h') =
      A.homogeneousPicardSheaf.obj.map (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b).op
        (pairPoincareClass A D L h) := by
  let q := (⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L, h⟩ : A.homogeneousPicardPresheaf.obj (.op D.scheme))
  let q' := (⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme)), h'⟩ :
    (A.pullback b).homogeneousPicardPresheaf.obj (.op (D.pullback b).scheme))
  have hc : (A.homogeneousPicardPresheafBaseChangeIso b).hom.app (.op (D.pullback b).scheme) q' =
      A.homogeneousPicardPresheaf.map (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b).op q :=
    Subtype.ext (PairPicardBaseChange.pairLinePullback_class A D b L)
  exact (A.toHomogeneousPicard_baseChange_apply b (D.pullback b).scheme q').trans
    ((congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
      (.op ((Over.map b).obj (D.pullback b).scheme))) hc).trans
        ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).naturality_apply
          (AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData.baseChangeProjection D b).op q))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClass
