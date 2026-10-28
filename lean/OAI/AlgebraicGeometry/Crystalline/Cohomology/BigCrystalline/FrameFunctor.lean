import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

/-! # Frame Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor

noncomputable section

/-! # The polynomial frame functions on the original big crystalline site -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps.BigCrystallineFrameMaps

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)} (a : σ → A)
  {Q P U : FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base}

theorem map_id (Q : FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base) : FrameMaps.BigCrystallineFrameMaps.ambientMap a (𝟙 Q) = AlgHom.id W _ := by
  have he : (FrameMaps.BigCrystallineFrameMaps.ambientMap a (𝟙 Q)).toRingHom =
      RingHom.id (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) := by
    apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate Q.ring σ Q.ideal Q.dividedPowers
      (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.ring σ Q.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ Q.ideal Q.dividedPowers)
      _ _ (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a (𝟙 Q)) ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
    · intro t
      exact FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a (𝟙 Q) t
    · intro i
      change FrameMaps.BigCrystallineFrameMaps.ambientMap a (𝟙 Q) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i
      rw [FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate, FrameLifts.BigCrystallineFrameLifts.translation_id, map_zero, zero_add]
  exact AlgHom.ext (RingHom.congr_fun he)

theorem map_comp (f : Q ⟶ P) (g : P ⟶ U) :
    FrameMaps.BigCrystallineFrameMaps.ambientMap a (f ≫ g) = (FrameMaps.BigCrystallineFrameMaps.ambientMap a f).comp (FrameMaps.BigCrystallineFrameMaps.ambientMap a g) := by
  have he : (FrameMaps.BigCrystallineFrameMaps.ambientMap a (f ≫ g)).toRingHom =
      ((FrameMaps.BigCrystallineFrameMaps.ambientMap a f).comp (FrameMaps.BigCrystallineFrameMaps.ambientMap a g)).toRingHom := by
    apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate U.ring σ U.ideal U.dividedPowers
      (DividedPowerAlgebra Q.ring (σ →₀ Q.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.ring σ Q.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ Q.ideal Q.dividedPowers)
      _ _ (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a (f ≫ g))
      ((FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f).comp _ (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a g))
    · intro t
      exact (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a (f ≫ g) t).trans
        ((congrArg (FrameMaps.BigCrystallineFrameMaps.ambientMap a f) (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a g t)).trans
          (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f (g.ringMap.toRingHom t))).symm
    · intro i
      change FrameMaps.BigCrystallineFrameMaps.ambientMap a (f ≫ g) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.ring σ 1 i) =
        FrameMaps.BigCrystallineFrameMaps.ambientMap a f (FrameMaps.BigCrystallineFrameMaps.ambientMap a g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.ring σ 1 i))
      rw [FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate, FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate, map_add, FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient,
        FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate, FrameLifts.BigCrystallineFrameLifts.translation_comp, map_add]
      ac_rfl
  exact AlgHom.ext (RingHom.congr_fun he)

def functions : (FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base)ᵒᵖ ⥤ ModuleCat W where
  obj Q := ModuleCat.of W (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
  map f := ModuleCat.ofHom (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop).toLinearMap
  map_id Q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact DFunLike.congr_fun (BigCrystallineFrameFunctor.map_id a Q.unop) t
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact DFunLike.congr_fun (BigCrystallineFrameFunctor.map_comp a g.unop f.unop) t

def coefficients : NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
    (p := p) (J := J) (δ := δ) base ⟶ functions a where
  app Q := ModuleCat.ofHom (IsScalarTower.toAlgHom W Q.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))).toLinearMap
  naturality {Q P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f.unop t).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor
