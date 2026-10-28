import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineFrobenius

/-! # Crystalline Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius

noncomputable section

/-!
# IntegralComparison: Frobenius on the original small crystalline cohomology of a separated scheme

The proved big-to-small cohomology equivalence transports the actual
scheme-induced Frobenius to the original small-site cohomology. The
comparison intertwines the two operators, also after rationalization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [Fintype k]
variable (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]
variable (a : ℕ) (hcard : Fintype.card k = p ^ a) (n : ℕ)

local notation "W" => WittVector p k
local notation "K₀" => FractionRing (WittVector p k)
local notation "SmallIntegral" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X n

def integralFrobenius : SmallIntegral →ₗ[W] SmallIntegral :=
  (Crystalline.Comparison.integralEquivWitt p k X n).toLinearMap.comp
    ((BigCrystallineFrobenius.integralFrobenius p k X a hcard n).comp
      (Crystalline.Comparison.integralEquivWitt p k X n).symm.toLinearMap)

lemma integral_intertwines : (integralFrobenius p k X a hcard n).comp (Crystalline.Comparison.integralEquivWitt p k X n).toLinearMap =
    (Crystalline.Comparison.integralEquivWitt p k X n).toLinearMap.comp
      (BigCrystallineFrobenius.integralFrobenius p k X a hcard n) := by
  apply LinearMap.ext
  intro x
  change Crystalline.Comparison.integralEquivWitt p k X n
      (BigCrystallineFrobenius.integralFrobenius p k X a hcard n
        ((Crystalline.Comparison.integralEquivWitt p k X n).symm (Crystalline.Comparison.integralEquivWitt p k X n x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def rationalFrobenius : Witt.Crystalline.rationalCohomology p k X n →ₗ[K₀]
    Witt.Crystalline.rationalCohomology p k X n :=
  (integralFrobenius p k X a hcard n).baseChange K₀

omit a hcard in
def rationalEquiv : BigCrystallineFrobenius.RationalCohomology p k X n ≃ₗ[K₀]
    Witt.Crystalline.rationalCohomology p k X n :=
  (Crystalline.Comparison.integralEquivWitt p k X n).baseChange W K₀ _ _

lemma rational_intertwines : (rationalFrobenius p k X a hcard n).comp (rationalEquiv p k X n).toLinearMap =
    (rationalEquiv p k X n).toLinearMap.comp
      (BigCrystallineFrobenius.rationalFrobenius p k X a hcard n) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    change b ⊗ₜ[W] integralFrobenius p k X a hcard n (Crystalline.Comparison.integralEquivWitt p k X n x) =
      b ⊗ₜ[W] Crystalline.Comparison.integralEquivWitt p k X n
        (BigCrystallineFrobenius.integralFrobenius p k X a hcard n x)
    exact congrArg (fun y => b ⊗ₜ[W] y)
      (DFunLike.congr_fun (integral_intertwines p k X a hcard n) x)
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius
