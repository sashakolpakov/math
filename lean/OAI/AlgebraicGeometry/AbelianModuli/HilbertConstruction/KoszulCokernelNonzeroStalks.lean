import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulCokernelStalk
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LineBundleCommonFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkSupportTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelSupport

/-! # Koszul Cokernel Nonzero Stalks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulCokernelNonzeroStalks

noncomputable section

/-! Every common zero has a nonzero stalk in the actual mixed Koszul
cokernel. Consequently its coherent support is exactly the common zero
set. This uses local frames and canonical pullback comparisons. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance cokernelLineBundle_quasicoherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    L.sheaf.IsQuasicoherent := L.isQuasicoherent
local instance cokernelLineBundle_finiteType {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    L.sheaf.IsFiniteType := L.isFiniteType

theorem modulePullback_open_stalk_isZero_iff {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (y : Y) :
    IsZero ((Module.StalkExactness.moduleStalkFunctor y).obj ((Scheme.Modules.pullback f).obj M)) ↔
      IsZero ((Module.StalkExactness.moduleStalkFunctor (f y)).obj M) := by
  rw [Module.StalkSupportTransport.moduleStalk_isZero_iff_additive, Module.StalkSupportTransport.moduleStalk_isZero_iff_additive]
  let G := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let e := G.mapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm ≪≫
    (Scheme.Modules.restrictStalkNatIso f y).app M
  exact e.isZero_iff

def mixedKoszulCokernelPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    (Scheme.Modules.pullback f).obj (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs) ≅
      MixedKoszulCokernelEuler.mixedKoszulCokernel ((Scheme.Modules.pullback f).obj M) (bs.map (MixedKoszulPullbackComplex.pullbackLineBundleSection f)) :=
  PreservesCokernel.iso (Scheme.Modules.pullback f) ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).d (-1) 0) ≪≫
    ScalarKoszul.CoefficientCokernel.cochainFinalCokernelIso (MixedKoszulPullbackComplex.mixedKoszulPullbackIso f M bs)

theorem mixedKoszulCokernel_stalk_nonzero {X : Scheme.{u}}
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (x : X) (hx : x ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs) :
    ¬ IsZero ((Module.StalkExactness.moduleStalkFunctor x).obj (MixedKoszulCokernelEuler.mixedKoszulCokernel M.sheaf bs)) := by
  obtain ⟨U, hxU, _, ⟨eM⟩, frames⟩ := Finite.LineBundleCommonFrames.mixedKoszul_common_affine_frame M bs x
  let y : U.toScheme := ⟨x, hxU⟩
  let cs := bs.map (MixedKoszulPullbackComplex.pullbackLineBundleSection U.ι)
  have hy : y ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet cs := by rw [MixedKoszulPullbackComplex.mixedSectionZeroSet_pullback]; exact hx
  have hn := Framed.MixedKoszulCokernelStalk.framedMixedKoszulCokernel_stalk_nonzero y (M.pullback U.ι).sheaf eM cs frames hy
  intro hz
  have hp : IsZero ((Module.StalkExactness.moduleStalkFunctor y).obj
      ((Scheme.Modules.pullback U.ι).obj (MixedKoszulCokernelEuler.mixedKoszulCokernel M.sheaf bs))) :=
    (modulePullback_open_stalk_isZero_iff U.ι (MixedKoszulCokernelEuler.mixedKoszulCokernel M.sheaf bs) y).mpr hz
  exact hn (((Module.StalkExactness.moduleStalkFunctor y).mapIso (mixedKoszulCokernelPullbackIso U.ι M.sheaf bs)).isZero_iff.mp hp)

theorem mixedKoszulCokernel_support_eq {X : Scheme.{u}}
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).1
    letI := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).2
    ((Coherent.Annihilator.coherentAnnihilator (MixedKoszulCokernelEuler.mixedKoszulCokernel M.sheaf bs)).support : Set X) = MixedKoszulGeometricSupport.mixedSectionZeroSet bs := by
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).1
  have := (MixedKoszulCokernelEuler.mixedKoszulCokernel_coherent M.sheaf bs).2
  apply Set.Subset.antisymm (MixedKoszulCokernelSupport.mixedKoszulCokernel_support_le M.sheaf bs)
  intro x hx
  exact Module.StalkSupportTransport.nonzero_moduleStalk_mem_coherent_support _ x (mixedKoszulCokernel_stalk_nonzero M bs x hx)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulCokernelNonzeroStalks
