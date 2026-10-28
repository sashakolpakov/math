import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackSpec
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

/-! # Tensor Pullback Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackOpen.Construction.TensorPullbackMap

noncomputable section

/-! The tensor-power pullback comparison is invertible on open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

universe u

variable {X Y : Scheme.{u}}

theorem open_compatibility (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules) (n : ℕ) :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) ≫
        TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n =
      (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).inv ≫
        AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app L) n := by
  have he (M : Y.Modules) : ((Scheme.Modules.restrictAdjunction f).homEquiv _ _)
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  have hu : (Scheme.Modules.restrictAdjunction f).unit.app L ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app L) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have hi : (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L n).postcomp
      (((Scheme.Modules.restrictAdjunction f).homEquiv _ _) (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n).inv) =
        ((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear (L.restrict f) n).pushforward f).precomp
          ((Scheme.Modules.restrictAdjunction f).unit.app L) := by
    have h := AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.restrictHomEquiv_postcomp (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L n)
      f (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictInv f L n)
    rw [AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictInv_spec] at h
    exact h.symm
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, he,
    Adjunction.homEquiv_naturality_right]
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
    (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n) = _
  rw [TensorPullbackSpec.Construction.TensorPullbackMap.homEquiv_comparison]
  apply AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPower_hom_ext
  rw [TensorPullbackSpec.Construction.TensorPullbackMap.adjunct_spec, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, hi,
    ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, ← AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_postcomp,
    AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec, AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.pushforward_precomp,
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp, hu]

theorem isIso_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (L : Y.Modules) (n : ℕ) : IsIso (TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n) := by
  have : IsIso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app L) n) :=
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).map_isIso _
  have h : IsIso ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) ≫
      TensorPullbackSpec.Construction.TensorPullbackMap.comparison f L n) := (open_compatibility f L n).symm ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackOpen.Construction.TensorPullbackMap
