import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.InversionBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Inversion Graph -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual inversion-graph bundle commutes with every base change
through the transported inverse operation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem InversionGraph.groupInversion_baseChange
    {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [GrpObj X] :
    ι[(Over.pullback f).obj X].left ≫ pullback.fst X.hom f =
      pullback.fst X.hom f ≫ ι[X].left :=
  Pullback.Comparisons.overPullback_map_left_fst ι[X] f

variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)

def PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundle_baseChangeIso :
    (A.inversionGraphBundle.pullback (pullback.fst A.abelian.scheme.hom f)).sheaf ≅
      (A.pullback f).inversionGraphBundle.sheaf := by
  let X := A.abelian.scheme
  let Y := (A.pullback f).abelian.scheme
  let a := pullback.fst X.hom f
  let G := A.graphBundle
  let e : (G.pullback a).sheaf ≅ (A.pullback f).graphBundle.sheaf :=
    (A.graphBundle_baseChangeIso f).symm
  let ei : ((G.pullback ι[X].left).pullback a).sheaf ≅
      ((A.pullback f).graphBundle.pullback ι[Y].left).sheaf :=
    (Scheme.Modules.pullbackComp a ι[X].left).app G.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (InversionGraph.groupInversion_baseChange f X).symm).app G.sheaf ≪≫
        (Scheme.Modules.pullbackComp ι[Y].left a).symm.app G.sheaf ≪≫
          (Scheme.Modules.pullback ι[Y].left).mapIso e
  exact Line.Bundles.LineBundle.tensorBaseChangeIso a G (G.pullback ι[X].left) ≪≫ Tensor.Bifunctor.tensorModuleMapIso e ei

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
