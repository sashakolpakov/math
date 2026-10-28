import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleLocalFactorization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenHomComparison

/-! # Open Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization.PicardOpenFactorization

noncomputable section

/-! Gluing native pullback factorizations through a module monomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleLocalFactorization.PicardModuleLocalFactorization OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenHomComparison.PicardOpenHomComparison

variable {X : Scheme.{u}} (M : X.Modules) {N P : X.Modules} (a : N ⟶ P)

theorem openHomEquiv_postcompose (U : X.Opens)
    (q : (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.obj (op U)) :
    OpenHomComparison.PicardOpenHomComparison.openHomEquiv M P U ((ModuleLocalFactorization.PicardModuleLocalFactorization.postcompose M a).app (op U) q) =
      OpenHomComparison.PicardOpenHomComparison.openHomEquiv M N U q ≫ (Scheme.Modules.pullback U.ι).map a := by
  let E := (Scheme.Modules.overEquiv U).functor
  let β := OpenHomComparison.PicardOpenHomComparison.openModuleIso U
  let r := ModuleHomSheaf.PicardModuleHomSheaf.moduleHomToOver M N U q
  change (β.app M).inv ≫ E.map (r ≫ a.over U) ≫ (β.app P).hom =
    ((β.app M).inv ≫ E.map r ≫ (β.app N).hom) ≫ (Scheme.Modules.pullback U.ι).map a
  rw [E.map_comp]
  simp only [Category.assoc]
  have hn : E.map (a.over U) ≫ (β.app P).hom =
      (β.app N).hom ≫ (Scheme.Modules.pullback U.ι).map a := β.hom.naturality a
  rw [hn]

theorem existsUnique_open_factorization [Mono a] (b : M ⟶ P)
    {ι : Type*} (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ iSup U)
    (q : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N)
    (hq : ∀ i, q i ≫ (Scheme.Modules.pullback (U i).ι).map a =
      (Scheme.Modules.pullback (U i).ι).map b) :
    ∃! c : M ⟶ N, c ≫ a = b := by
  apply ModuleLocalFactorization.PicardModuleLocalFactorization.existsUnique_local_factorization M a b U hU
    (fun i ↦ (OpenHomComparison.PicardOpenHomComparison.openHomEquiv M N (U i)).symm (q i))
  intro i
  apply (OpenHomComparison.PicardOpenHomComparison.openHomEquiv M P (U i)).injective
  rw [openHomEquiv_postcompose, Equiv.apply_symm_apply, OpenHomComparison.PicardOpenHomComparison.openHomEquiv_global, hq i]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenFactorization.PicardOpenFactorization
