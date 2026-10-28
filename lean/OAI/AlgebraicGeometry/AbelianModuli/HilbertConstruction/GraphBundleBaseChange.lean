import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AdditionBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Graph Bundle Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual addition-graph bundle commutes with every base change,
using the native product comparison and transported group law. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem GraphBundleBaseChange.groupMultiplication_productBaseChange
    {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [GrpObj X] :
    Graph.FamilyNaturality.overProductBaseChangeMap f X X ≫ μ[X].left =
      μ[(Over.pullback f).obj X].left ≫ pullback.fst X.hom f := by
  let c := Functor.Monoidal.μIso (Over.pullback f) X X
  change (c.hom.left ≫ pullback.fst (X ⊗ X).hom f) ≫ μ[X].left =
    (c.hom.left ≫ ((Over.pullback f).map μ[X]).left) ≫ pullback.fst X.hom f
  rw [Category.assoc, Category.assoc, Pullback.Comparisons.overPullback_map_left_fst]

variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)

def PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_baseChangeIso :
    (A.additionGraphBundle.pullback (Graph.FamilyNaturality.overProductBaseChangeMap f A.abelian.scheme A.abelian.scheme)).sheaf ≅
      (A.pullback f).additionGraphBundle.sheaf := by
  let X := A.abelian.scheme
  let Y := (A.pullback f).abelian.scheme
  let a := pullback.fst X.hom f
  let c := Graph.FamilyNaturality.overProductBaseChangeMap f X X
  let G := A.graphBundle
  let e : (G.pullback a).sheaf ≅ (A.pullback f).graphBundle.sheaf :=
    (A.graphBundle_baseChangeIso f).symm
  let eext : ((Graph.ExternalTensorBundle.externalTensorBundle G G).pullback c).sheaf ≅
      (Graph.ExternalTensorBundle.externalTensorBundle (A.pullback f).graphBundle (A.pullback f).graphBundle).sheaf :=
    External.TensorBaseChange.externalTensorBundle_baseChangeIso f G G ≪≫
      Tensor.Bifunctor.tensorModuleMapIso ((Scheme.Modules.pullback (fst Y Y).left).mapIso e)
        ((Scheme.Modules.pullback (snd Y Y).left).mapIso e)
  let emul : ((G.pullback μ[X].left).pullback c).sheaf ≅
      ((A.pullback f).graphBundle.pullback μ[Y].left).sheaf :=
    (Scheme.Modules.pullbackComp c μ[X].left).app G.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (GraphBundleBaseChange.groupMultiplication_productBaseChange f X)).app G.sheaf ≪≫
        (Scheme.Modules.pullbackComp μ[Y].left a).symm.app G.sheaf ≪≫
          (Scheme.Modules.pullback μ[Y].left).mapIso e
  exact Line.Bundles.LineBundle.tensorBaseChangeIso c (Graph.ExternalTensorBundle.externalTensorBundle G G) (G.pullback μ[X].left) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso eext emul

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
