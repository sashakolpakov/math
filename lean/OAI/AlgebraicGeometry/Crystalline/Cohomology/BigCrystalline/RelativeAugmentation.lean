import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.AugmentationFormula

/-! # Relative Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeAugmentation.BigCrystallineRelativeAugmentation

noncomputable section

/-! # The original structure augmentation in actual relative PD coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)}
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf
  (p := p) (J := J) (δ := δ) base
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a

def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj G ⟶
    RelativeForms.BigCrystallineRelativeForms.complex a :=
  α ≫ (RelativeForms.BigCrystallineRelativeForms.complexIso a).hom

omit [LinearOrder σ] in
theorem original_zero (Q : Cᵒᵖ) (x : (G).obj Q) :
    (((α).f 0).app Q).hom x =
      algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x ⊗ₜ[W]
        (exteriorPower.zeroEquiv W (σ →₀ W)).symm 1 := by
  exact Koszul.AugmentationFormula.KoszulAugmentationFormula.zero W σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q x

theorem augmentation_component (Q : Cᵒᵖ) (x : (G).obj Q) :
    (((augmentation a).f 0).app Q).hom x =
      ((FreeRelative.ScalarComparison.FreeRelativeScalarComparison.complexIso W Q.unop.ring σ
        Q.unop.ideal Q.unop.dividedPowers).hom.f 0).hom ((((α).f 0).app Q).hom x) := rfl

theorem zero (Q : Cᵒᵖ) (x : (G).obj Q) :
    (((augmentation a).f 0).app Q).hom x =
      PD.DeRham.PDDeRham.symbol Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring))
        (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.unop.ring σ Q.unop.ideal)
        (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers)
        (algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x)
        Fin.elim0 := by
  change Q.unop.ring at x
  let e := ((FreeRelative.ScalarComparison.FreeRelativeScalarComparison.complexIso W Q.unop.ring σ
    Q.unop.ideal Q.unop.dividedPowers).hom.f 0).hom
  have ha := original_zero a Q x
  have hw : (exteriorPower.zeroEquiv W (σ →₀ W)).symm 1 =
      exteriorPower.ιMulti W 0 (fun j => Finsupp.single (Fin.elim0 j : σ) 1) := by
    apply (exteriorPower.zeroEquiv W (σ →₀ W)).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]
  rw [hw] at ha
  have h₁ := congrArg e ha
  have h₂ := FreeRelative.ScalarComparison.FreeRelativeScalarComparison.word W Q.unop.ring σ Q.unop.ideal Q.unop.dividedPowers
    0 (algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x) Fin.elim0
  have ht : Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.unop.ring σ 1 ∘ Fin.elim0 =
      (Fin.elim0 : Fin 0 → DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) := by
    funext j
    exact Fin.elim0 j
  rw [ht] at h₂
  exact (augmentation_component a Q x).trans (h₁.trans h₂)

instance augmentation_quasiIso : QuasiIso (augmentation (p := p) (J := J) (δ := δ) (base := base) a) := by
  unfold augmentation
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.RelativeAugmentation.BigCrystallineRelativeAugmentation
