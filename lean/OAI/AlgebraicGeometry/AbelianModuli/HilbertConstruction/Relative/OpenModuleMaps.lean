import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement

/-! # Open Module Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenModuleMaps

noncomputable section

/-! Module maps on the open subsets of a scheme over a fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (T : Over X)

def relativeOpen (U : T.left.Opens) : Over X :=
  (Over.map T.hom).obj (OpenModule.MapRefinement.openSubsetOver U)

def relativeOpenInclusion (U : T.left.Opens) : relativeOpen T U ⟶ T := Over.homMk U.ι rfl

def relativeOpenMap {U V : T.left.Opens} (h : U ≤ V) : relativeOpen T U ⟶ relativeOpen T V :=
  (Over.map T.hom).map (OpenModule.MapRefinement.openSubsetOverMap h)

theorem relativeOpenMap_inclusion {U V : T.left.Opens} (h : U ≤ V) :
    relativeOpenMap T h ≫ relativeOpenInclusion T V = relativeOpenInclusion T U := by
  apply Over.OverMorphism.ext
  exact T.left.homOfLE_ι h

theorem moduleMapPullbackAlong_relativeOpen (M N : X.Modules) (U : T.left.Opens)
    (φ : (Scheme.Modules.pullback T.hom).obj M ⟶ (Scheme.Modules.pullback T.hom).obj N) :
    Module.MapSlicePullback.moduleMapPullbackAlong (relativeOpenInclusion T U) φ =
      Module.HomBaseChange.moduleHomBaseChangeEquiv T.hom M N (OpenModule.MapRefinement.openSubsetOver U) ((Scheme.Modules.pullback U.ι).map φ) :=
  rfl

theorem moduleHomBaseChangeEquiv_symm_naturality {Y : Scheme.{u}} (g : Y ⟶ X)
    (M N : X.Modules) {U V : Over Y} (a : U ⟶ V)
    (φ : (Module.HomPresheaf.moduleHomPresheaf M N).obj (.op ((Over.map g).obj V))) :
    Module.MapSlicePullback.moduleMapPullbackAlong a ((Module.HomBaseChange.moduleHomBaseChangeEquiv g M N V).symm φ) =
      (Module.HomBaseChange.moduleHomBaseChangeEquiv g M N U).symm (Module.MapSlicePullback.moduleMapPullbackAlong ((Over.map g).map a) φ) := by
  apply (Module.HomBaseChange.moduleHomBaseChangeEquiv g M N U).injective
  rw [Module.HomBaseChange.moduleHomBaseChangeEquiv_naturality, Equiv.apply_symm_apply]
  exact ((Module.HomBaseChange.moduleHomBaseChangeEquiv g M N U).apply_symm_apply _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenModuleMaps
