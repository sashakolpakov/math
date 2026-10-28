import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent

/-! # Open Module Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech

noncomputable section

/-! Native descent comparisons on literal open subsets, proved with
arbitrary recovered modules before specializing to open direct images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery.NativeModuleDescentRecovery

private def cechOfRestrictions {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (M : ι → X.Modules)
    (e : ∀ V : X.Opens, ∀ i j, V ≤ U i → V ≤ U j →
      ((Scheme.Modules.pullback V.ι).obj (M i) ≅ (Scheme.Modules.pullback V.ι).obj (M j)))
    (hid : ∀ V i (h : V ≤ U i), e V i i h h = Iso.refl _)
    (hcomp : ∀ V i j k (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
      (e V i j hi hj).hom ≫ (e V j k hj hk).hom = (e V i k hi hk).hom)
    (hrefine : ∀ {V W : X.Opens} (h : W ≤ V) i j (hi : V ≤ U i) (hj : V ≤ U j),
      Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) (e V i j hi hj).hom =
        (e W i j (h.trans hi) (h.trans hj)).hom) : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U M where
  iso i j := e (U i ⊓ U j) i j inf_le_left inf_le_right
  identity i := hid (U i ⊓ U i) i inf_le_left
  cocycle i j k := by
    let V := (U i ⊓ U j) ⊓ U k
    have a := hrefine (show V ≤ U i ⊓ U j from inf_le_left) i j inf_le_left inf_le_right
    have b := hrefine (show V ≤ U j ⊓ U k from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right) j k inf_le_left inf_le_right
    have c := hrefine (show V ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right) i k inf_le_left inf_le_right
    exact (congrArg₂ (fun x y => x ≫ y) a b).trans
      ((hcomp V i j k (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) inf_le_right).trans c.symm)

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun i => (U i).ι))
  (M : ι → X.Modules)
  (r : ∀ i, (Scheme.Modules.pullback (U i).ι).obj (M i) ≅ D.obj i)

def onOpen (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (Scheme.Modules.pullback V.ι).obj (M i) ≅
      (Scheme.Modules.pullback V.ι).obj (M j) :=
  ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso D M r V.ι i j
    (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)

private theorem onOpen_hom (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (onOpen U D M r V i j hi hj).hom =
      (ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso D M r V.ι i j
        (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)).hom := rfl

private theorem openInclusion_comp {V W Z : X.Opens} (h : W ≤ V) (k : V ≤ Z) :
    X.homOfLE h ≫ X.homOfLE k = X.homOfLE (h.trans k) := by
  apply (cancel_mono Z.ι).mp
  rw [Category.assoc, X.homOfLE_ι k, X.homOfLE_ι h, X.homOfLE_ι (h.trans k)]

theorem onOpen_refine {V W : X.Opens} (h : W ≤ V) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) (onOpen U D M r V i j hi hj).hom =
      (onOpen U D M r W i j (h.trans hi) (h.trans hj)).hom := by
  exact (ModuleDescentRecovery.moduleMapPullbackAlong_eq_pullHom (OpenModule.MapRefinement.openSubsetOverMap h)
    (onOpen U D M r V i j hi hj).hom).trans
    (ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_pullback D M r
    (X.homOfLE h) V.ι W.ι (X.homOfLE_ι h) i j
    (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)
    (X.homOfLE (h.trans hi)) (X.homOfLE (h.trans hj))
    (X.homOfLE_ι (h.trans hi)) (X.homOfLE_ι (h.trans hj))
    (openInclusion_comp h hi) (openInclusion_comp h hj))

private theorem onOpen_cocycle (V : X.Opens) (i j k : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    (onOpen U D M r V i j hi hj).hom ≫ (onOpen U D M r V j k hj hk).hom =
      (onOpen U D M r V i k hi hk).hom := by
  have a := onOpen_hom U D M r V i j hi hj
  have b := onOpen_hom U D M r V j k hj hk
  have c := onOpen_hom U D M r V i k hi hk
  exact (congrArg₂ (fun x y => x ≫ y) a b).trans
    ((ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_comp D M r V.ι i j k
      (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE hk)
      (X.homOfLE_ι hi) (X.homOfLE_ι hj) (X.homOfLE_ι hk)).trans c.symm)

def cech : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U M :=
  cechOfRestrictions U M (onOpen U D M r)
    (fun V i hi => ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_self D M r V.ι i (X.homOfLE hi) (X.homOfLE_ι hi))
    (onOpen_cocycle U D M r) (onOpen_refine U D M r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech
