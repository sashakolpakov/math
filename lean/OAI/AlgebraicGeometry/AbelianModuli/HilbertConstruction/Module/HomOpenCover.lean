import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenModuleMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Hom Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomOpenCover

noncomputable section

/-! The presheaf of module maps satisfies gluing on every open-subset cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} (M N : X.Modules) (T : Over X) {ι : Type v} (U : ι → T.left.Opens)

theorem moduleHom_openCover_injective (hU : ∀ x : T.left, ∃ i, x ∈ U i)
    (φ ψ : (HomPresheaf.moduleHomPresheaf M N).obj (.op T))
    (h : ∀ i, (HomPresheaf.moduleHomPresheaf M N).map (Relative.OpenModuleMaps.relativeOpenInclusion T (U i)).op φ =
      (HomPresheaf.moduleHomPresheaf M N).map (Relative.OpenModuleMaps.relativeOpenInclusion T (U i)).op ψ) : φ = ψ := by
  apply MapCoverEquality.moduleMap_eq_of_pullback_cover U hU
  intro i
  apply (HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver (U i))).injective
  exact (Relative.OpenModuleMaps.moduleMapPullbackAlong_relativeOpen T M N (U i) φ).symm.trans
    ((h i).trans (Relative.OpenModuleMaps.moduleMapPullbackAlong_relativeOpen T M N (U i) ψ))

def moduleHomOpenCoverData
    (s : ∀ i, (HomPresheaf.moduleHomPresheaf M N).obj (.op (Relative.OpenModuleMaps.relativeOpen T (U i))))
    (hs : Presieve.Arrows.Compatible (HomPresheaf.moduleHomPresheaf M N)
      (fun i => Relative.OpenModuleMaps.relativeOpenInclusion T (U i)) s) :
    OpenPullback.MapGluing.OpenPullbackModuleMaps U ((Scheme.Modules.pullback T.hom).obj M)
      ((Scheme.Modules.pullback T.hom).obj N) where
  localMap i := (HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver (U i))).symm (s i)
  agree i j V hi hj := by
    have h := hs i j (Relative.OpenModuleMaps.relativeOpen T V) (Relative.OpenModuleMaps.relativeOpenMap T hi) (Relative.OpenModuleMaps.relativeOpenMap T hj)
      ((Relative.OpenModuleMaps.relativeOpenMap_inclusion T hi).trans (Relative.OpenModuleMaps.relativeOpenMap_inclusion T hj).symm)
    exact (Relative.OpenModuleMaps.moduleHomBaseChangeEquiv_symm_naturality T.hom M N (OpenModule.MapRefinement.openSubsetOverMap hi) (s i)).trans
      ((congrArg (HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver V)).symm h).trans
        (Relative.OpenModuleMaps.moduleHomBaseChangeEquiv_symm_naturality T.hom M N (OpenModule.MapRefinement.openSubsetOverMap hj) (s j)).symm)

theorem moduleHom_isSheafFor_openCover (hU : ∀ x : T.left, ∃ i, x ∈ U i) :
    Presieve.IsSheafFor (HomPresheaf.moduleHomPresheaf M N)
      (Presieve.ofArrows (fun i => Relative.OpenModuleMaps.relativeOpen T (U i)) (fun i => Relative.OpenModuleMaps.relativeOpenInclusion T (U i))) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  let D := moduleHomOpenCoverData M N T U s hs
  have hg : ∀ i, (HomPresheaf.moduleHomPresheaf M N).map (Relative.OpenModuleMaps.relativeOpenInclusion T (U i)).op (D.glue hU) = s i := by
    intro i
    exact (Relative.OpenModuleMaps.moduleMapPullbackAlong_relativeOpen T M N (U i) (D.glue hU)).trans
      ((congrArg (HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver (U i)))
        (D.glue_pullback hU i)).trans
          ((HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver (U i))).apply_symm_apply (s i)))
  refine ⟨D.glue hU, hg, ?_⟩
  intro φ hφ
  exact moduleHom_openCover_injective M N T U hU φ (D.glue hU) (fun i => (hφ i).trans (hg i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomOpenCover
