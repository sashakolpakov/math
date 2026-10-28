import OAI.AlgebraicGeometry.Comparison.Betti.FrameGeneratorCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Frame Generator Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameGeneratorRestriction.RingedModules

noncomputable section

/-! The generator of a restricted actual line frame is the original module
restriction of its generator. -/

open _root_.CategoryTheory Opposite

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  (S : Sheaf J RingCat.{0}) (M : SheafOfModules.{0} S)

def overFrameGenerator (U : C) (e : M.over U ≅ SheafOfModules.unit (S.over U)) :
    M.val.obj (op U) := e.inv.val.app (op (Over.mk (𝟙 U))) (1 : S.obj.obj (op U))

theorem overFrameGenerator_restrict {U V : C} (f : V ⟶ U)
    (e : M.over U ≅ SheafOfModules.unit (S.over U)) :
    overFrameGenerator S M V
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization S M U e (Over.mk f)) =
      M.val.map f.op (overFrameGenerator S M U e) := by
  let W : Over U := (Over.map f).obj (Over.mk (𝟙 V))
  let q : W ⟶ Over.mk (𝟙 U) := Over.homMk f (by
    change f ≫ 𝟙 U = 𝟙 V ≫ f
    rw [Category.comp_id, Category.id_comp])
  have h := PresheafOfModules.naturality_apply e.inv.val q.op (1 : S.obj.obj (op U))
  have hone := (S.obj.map f.op).hom.map_one
  exact (congrArg (fun r : S.obj.obj (op V) => e.inv.val.app (op W) r) hone).symm.trans h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.FrameGeneratorRestriction.RingedModules
