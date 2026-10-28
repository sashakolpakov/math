import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.AdjointUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenFrames

/-! # Pullback Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism

noncomputable section

/-! The explicit pulled-back transition sheaf is canonically isomorphic to the actual sheaf pullback, by the proved universal property of its local frame images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
variable (hU : ∀ y : Y, ∃ i, y ∈ U i)

include hU in
theorem openFramePullbackAdjoint_injective (N : X.Modules) :
    Function.Injective (fun φ : ModuleSheaf.openFrameModuleSheaf (D.pullback f) ⟶ N =>
      PullbackSheafMap.openFramePullbackAdjoint D f ≫ (Scheme.Modules.pushforward f).map φ) := by
  intro φ ψ h
  exact (AdjointUniqueness.openFrameAdjointLift_unique D f hU _ φ rfl).trans
    (AdjointUniqueness.openFrameAdjointLift_unique D f hU _ ψ h.symm).symm

theorem openFramePullbackComparison_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ModuleSheaf.openFrameModuleSheaf D) ≫
      (Scheme.Modules.pushforward f).map (PullbackSheafMap.openFramePullbackComparison D f) = PullbackSheafMap.openFramePullbackAdjoint D f :=
  (Adjunction.homEquiv_unit _ _ _ (PullbackSheafMap.openFramePullbackComparison D f)).symm.trans
    (PullbackSheafMap.openFramePullbackComparison_adjoint D f)

def openFramePullbackInverse :
    ModuleSheaf.openFrameModuleSheaf (D.pullback f) ⟶ (Scheme.Modules.pullback f).obj (ModuleSheaf.openFrameModuleSheaf D) :=
  AdjointLift.openFrameAdjointLift D f hU ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ModuleSheaf.openFrameModuleSheaf D))

theorem openFramePullbackComparison_inverse :
    PullbackSheafMap.openFramePullbackComparison D f ≫ openFramePullbackInverse D f hU = 𝟙 _ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    openFramePullbackComparison_unit]
  exact (AdjointRecovery.openFrameAdjointLift_spec D f hU _).trans
    (by
      rw [(Scheme.Modules.pushforward f).map_id]
      exact (Category.comp_id ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ModuleSheaf.openFrameModuleSheaf D))).symm)

theorem openFramePullbackInverse_comparison :
    openFramePullbackInverse D f hU ≫ PullbackSheafMap.openFramePullbackComparison D f = 𝟙 _ := by
  apply openFramePullbackAdjoint_injective D f hU
  change PullbackSheafMap.openFramePullbackAdjoint D f ≫ (Scheme.Modules.pushforward f).map
    (openFramePullbackInverse D f hU ≫ PullbackSheafMap.openFramePullbackComparison D f) =
      PullbackSheafMap.openFramePullbackAdjoint D f ≫ (Scheme.Modules.pushforward f).map (𝟙 _)
  have hm := (congrArg (fun a => PullbackSheafMap.openFramePullbackAdjoint D f ≫ a)
    ((Scheme.Modules.pushforward f).map_comp (openFramePullbackInverse D f hU) (PullbackSheafMap.openFramePullbackComparison D f))).trans
      (Category.assoc _ _ _).symm
  have he := AdjointRecovery.openFrameAdjointLift_spec D f hU
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (ModuleSheaf.openFrameModuleSheaf D))
  exact hm.trans ((congrArg (fun a => a ≫ (Scheme.Modules.pushforward f).map (PullbackSheafMap.openFramePullbackComparison D f)) he).trans
    ((openFramePullbackComparison_unit D f).trans (by
      rw [(Scheme.Modules.pushforward f).map_id]
      exact (Category.comp_id (PullbackSheafMap.openFramePullbackAdjoint D f)).symm)))

def openFramePullbackIso :
    (Scheme.Modules.pullback f).obj (ModuleSheaf.openFrameModuleSheaf D) ≅ ModuleSheaf.openFrameModuleSheaf (D.pullback f) where
  hom := PullbackSheafMap.openFramePullbackComparison D f
  inv := openFramePullbackInverse D f hU
  hom_inv_id := openFramePullbackComparison_inverse D f hU
  inv_hom_id := openFramePullbackInverse_comparison D f hU

def lineBundleFromOpenFrames_pullbackIso :
    ((LineBundle.FromOpenFrames.lineBundleFromOpenFrames D hU).pullback f).sheaf ≅
      (LineBundle.FromOpenFrames.lineBundleFromOpenFrames (D.pullback f) (PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover f hU)).sheaf :=
  openFramePullbackIso D f hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackIsomorphism
