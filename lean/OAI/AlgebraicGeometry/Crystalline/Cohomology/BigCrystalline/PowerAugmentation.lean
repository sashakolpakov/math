import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeAugmentation

/-! # Power Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerAugmentation.BigCrystallinePowerAugmentation

noncomputable section

/-! # Power-coordinate comparison preserves the actual structure augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)}
  (a : σ → A) (m : ℕ) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base

theorem relative :
    RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation (p := p) (J := J) (δ := δ) (base := base)
        (fun i => a i ^ m) ≫ PowerForms.BigCrystallinePowerForms.relativeComplexMap a m =
      RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation a := by
  apply HomologicalComplex.from_single_hom_ext
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Q.unop.ring at x
  let f := ((PowerForms.BigCrystallinePowerForms.component a m Q).f 0).hom
  have hs := congrArg f (RelativeAugmentation.BigCrystallineRelativeAugmentation.zero (fun i => a i ^ m) Q x)
  have ht := RelativeAugmentation.BigCrystallineRelativeAugmentation.zero a Q x
  let u := PowerForms.BigCrystallinePowerForms.ambientMap a m Q.unop
  have hf := PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap_symbol W Q.unop.ring
    (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
    (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
    u (PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a m Q.unop)
    0 (algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x) Fin.elim0
  rw [AlgHom.commutes] at hf
  have he : u ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) := by
    funext j
    exact Fin.elim0 j
  rw [he] at hf
  exact hs.trans (hf.trans ht.symm)

theorem original :
    FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base)
        (fun i => a i ^ m) ≫ PowerForms.BigCrystallinePowerForms.complexMap a m =
      FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a := by
  let e := RelativeForms.BigCrystallineRelativeForms.complexIso (p := p) (J := J) (δ := δ) (base := base) a
  let Z := (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat.{u} W)).obj
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base)
  have h := congrArg (fun t : Z ⟶ RelativeForms.BigCrystallineRelativeForms.complex
      (p := p) (J := J) (δ := δ) (base := base) a => t ≫ e.inv)
    (relative (p := p) (J := J) (δ := δ) (base := base) a m)
  simpa only [PowerForms.BigCrystallinePowerForms.complexMap, RelativeAugmentation.BigCrystallineRelativeAugmentation.augmentation,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, e] using h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerAugmentation.BigCrystallinePowerAugmentation
