import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism

/-! # Top Augmentation Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopAugmentationPullback

noncomputable section

/-! The original top-section Čech augmentation commutes with the actual coefficient pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
  (F : TopCat.Sheaf AddCommGrpCat.{0} X) (G : TopCat.Sheaf AddCommGrpCat.{0} Y)
  (α : F.obj ⟶ (Opens.map f).op ⋙ G.obj)

theorem additiveCechPullback_topAugmentation
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤) :
    SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation U F ≫ (PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G α).f 0 =
      α.app (op ⊤) ≫ SheafCohomology.Cech.TopZeroCycles.TopCat.Sheaf.cechTopSectionsAugmentation (fun i => (Opens.map f).obj (U i)) G := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact congrArg Subtype.val (PullbackGlobalIsomorphism.additiveCechPullbackMap_global_zeroCycle f U F G α hU hV x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.TopAugmentationPullback
