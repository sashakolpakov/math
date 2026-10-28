import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Data.Fintype.Order

/-! # Product Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductLocalization

noncomputable section

/-! Finite categorical products preserve denominator clearing and the
power-torsion kernel property of localization maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
variable {R : Type u} [CommRing R] (r : R) {ι : Type v} [Finite ι]
  (M N : ι → ModuleCat.{max v w} R) [HasProduct M] [HasProduct N]
  (q : ∀ i, M i ⟶ N i)

theorem surj (h : ∀ i (y : N i), ∃ (a : ℕ) (x : M i), r^a • y = q i x)
    (y : (∏ᶜ N : ModuleCat.{max v w} R)) :
    ∃ (a : ℕ) (x : (∏ᶜ M : ModuleCat.{max v w} R)), r^a • y = Limits.Pi.map q x := by
  choose a x hx using fun i => h i (Pi.π N i y)
  obtain ⟨b, hb⟩ := Finite.exists_le a
  obtain ⟨v, hv⟩ := IntegralComparison.Module.ProductScalarKernel.exists_coordinates M (fun i => r^(b-a i) • x i)
  refine ⟨b, v, IntegralComparison.Module.ProductScalarKernel.element_ext N _ _ (fun i => ?_)⟩
  rw [map_smul]
  have hm := ConcreteCategory.congr_hom (Pi.map_π q i) v
  change Pi.π N i (Limits.Pi.map q v) = q i (Pi.π M i v) at hm
  rw [hm, hv, map_smul, ← hx, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hb i)]

theorem kernel (h : ∀ i (x : M i), q i x = 0 → ∃ a : ℕ, r^a • x = 0)
    (x : (∏ᶜ M : ModuleCat.{max v w} R)) (hx : Limits.Pi.map q x = 0) :
    ∃ a : ℕ, r^a • x = 0 := by
  have hi (i : ι) : q i (Pi.π M i x) = 0 :=
    (ConcreteCategory.congr_hom (Pi.map_π q i) x).symm.trans
      ((congrArg (Pi.π N i) hx).trans (Pi.π N i).hom.map_zero)
  choose a ha using fun i => h i _ (hi i)
  obtain ⟨b, hb⟩ := Finite.exists_le a
  refine ⟨b, IntegralComparison.Module.ProductScalarKernel.element_ext M _ _ (fun i => ?_)⟩
  rw [map_smul, map_zero, ← Nat.sub_add_cancel (hb i), pow_add, mul_smul, ha, smul_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductLocalization
