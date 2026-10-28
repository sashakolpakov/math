import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLifts

/-! # Relative Form Symbols -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeFormSymbols.BigCrystallineRelativeFormSymbols

noncomputable section

/-! # The original relative frame maps on differential-form symbols -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J}
  {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)} (a : σ → A)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base

theorem map_symbol {Q P : Cᵒᵖ} (f : Q ⟶ P) (j : ℕ)
    (b : DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (v : Fin j → DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) :
    ((RelativeForms.BigCrystallineRelativeForms.map a f).f j).hom
      (PD.DeRham.PDDeRham.symbol Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
        (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
        (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) b v) =
    PD.DeRham.PDDeRham.symbol P.unop.ring (DividedPowerAlgebra P.unop.ring (σ →₀ P.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal P.unop.ring σ P.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.unop.ring σ P.unop.ideal P.unop.dividedPowers)
      (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop b) ((FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop) ∘ v) :=
  PD.RelativeScalarMap.PDRelativeScalarMap.symbol W Q.unop.ring P.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (DividedPowerAlgebra P.unop.ring (σ →₀ P.unop.ring))
    f.unop.ringMap.toRingHom (fun w => DFunLike.congr_fun f.unop.overBase w)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f.unop).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f.unop)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal P.unop.ring σ P.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers P.unop.ring σ P.unop.ideal P.unop.dividedPowers)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f.unop) j b v

theorem power_symbol (m : ℕ) (Q : Cᵒᵖ) (j : ℕ)
    (b : DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (v : Fin j → DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) :
    ((PowerForms.BigCrystallinePowerForms.component a m Q).f j).hom
      (PD.DeRham.PDDeRham.symbol Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
        (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
        (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers) b v) =
    PD.DeRham.PDDeRham.symbol Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
      (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
      (PowerForms.BigCrystallinePowerForms.ambientMap a m Q.unop b) ((PowerForms.BigCrystallinePowerForms.ambientMap a m Q.unop) ∘ v) :=
  PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap_symbol W Q.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    (PowerForms.BigCrystallinePowerForms.ambientMap a m Q.unop)
    (PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a m Q.unop) j b v

theorem power_twist (base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
    (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
    (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) (m : ℕ) (Q : C) :
    (show DividedPowerAlgebra Q.ring (σ →₀ Q.ring) →ₐ[Q.ring] DividedPowerAlgebra Q.ring (σ →₀ Q.ring) from
      PowerForms.BigCrystallinePowerForms.ambientMap a m
        ((NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h).obj Q)) =
      PowerForms.BigCrystallinePowerForms.ambientMap a m Q := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeFormSymbols.BigCrystallineRelativeFormSymbols
