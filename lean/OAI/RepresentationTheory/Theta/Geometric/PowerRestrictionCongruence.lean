import OAI.RepresentationTheory.Theta.Geometric.MultilinearRestrictionComposition

/-! # Power Restriction Congruence -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerRestrictionCongruence

noncomputable section

/-! Tensor-power restriction respects equality of the open immersion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem multilinear_restrict_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] {L P : Y.Modules} {n : ℕ}
    (β : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P) :
    (β.restrict g).precomp ((Scheme.Modules.restrictFunctorCongr h).app L).hom =
      (β.restrict f).postcomp ((Scheme.Modules.restrictFunctorCongr h).app P).hom := by
  ext U s
  have hU : g ''ᵁ U = f ''ᵁ U := by simp [h]
  change (Fin n → Γ(L, f ''ᵁ U)) at s
  change (β.app (g ''ᵁ U)) (fun i => L.presheaf.map (eqToHom hU).op (s i)) =
    P.presheaf.map (eqToHom hU).op (β.app (f ''ᵁ U) s)
  exact (β.naturality (eqToHom hU) s).symm

theorem tensorPowerRestrictIso_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) (n : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).mapIso ((Scheme.Modules.restrictFunctorCongr h).app M) ≪≫
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso g M n =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso f M n ≪≫
      (Scheme.Modules.restrictFunctorCongr h).app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) := by
  apply Iso.ext
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPower_hom_ext
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear (M.restrict f) n).postcomp
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap ((Scheme.Modules.restrictFunctorCongr h).app M).hom n ≫
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictHom g M n) =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear (M.restrict f) n).postcomp
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictHom f M n ≫
        ((Scheme.Modules.restrictFunctorCongr h).app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n)).hom)
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap_spec,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec,
    multilinear_restrict_congr, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec]

end

end OAI.RepresentationTheory.Theta.Geometric.PowerRestrictionCongruence
