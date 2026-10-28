import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PrimaryTorsionCard
import OAI.NumberTheory.PadicHodge.IntegralComparison.TateKernelDeterminant
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision

/-! # Tate Finite Kernel Norm -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TateFiniteKernelNorm

noncomputable section

/-! The determinant of the native Tate action of a surjective map with
finite kernel has the same prime-adic norm as the kernel cardinality. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision

variable (p : ℕ) [Fact p.Prime] {A : Type*} [AddCommGroup A]
  [Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p A 1)] (f : A →+ A) [Finite f.ker]
  (hf : Function.Surjective f) (hdiv : ∀ x : A, ∃ y, p • y = x)

include hf hdiv

theorem determinant_valuation :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det.valuation = (Nat.card f.ker).factorization p := by
  let h := (Nat.card f.ker).factorization p
  let c := Nat.card f.ker / p ^ h
  let g := AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.inverseMultiple f hf
  have hc : p.Coprime c := Nat.coprime_ordCompl Fact.out (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.card_ne_zero f)
  have hmul : c * p ^ h = Nat.card f.ker := Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  have hfg (x : A) : f (g x) = c • ((p ^ h) • x) := by
    rw [smul_smul, hmul]
    exact DFunLike.congr_fun (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.comp_inverseMultiple f hf) x
  have hgf (x : A) : g (f x) = c • ((p ^ h) • x) := by
    rw [smul_smul, hmul]
    exact DFunLike.congr_fun (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.inverseMultiple_comp f hf) x
  have he := TateKernelDeterminant.primary_kernel_card_of_coprime p h f g c hc
    hfg hgf hdiv
  rw [IntegralComparison.Finite.PrimaryTorsionCard.card_torsion] at he
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le he).symm

theorem determinant_ne_zero : (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det ≠ 0 := by
  let : Module.Finite ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := A) p) :=
    AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion p hdiv
  let h := (Nat.card f.ker).factorization p
  let c := Nat.card f.ker / p ^ h
  let g := AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.inverseMultiple f hf
  have hc : p.Coprime c := Nat.coprime_ordCompl Fact.out (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.card_ne_zero f)
  obtain ⟨u, hu⟩ : IsUnit (c : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
  have hgf (x : A) : g (f x) = c • ((p ^ h) • x) := by
    rw [smul_smul, Nat.div_mul_cancel (Nat.ordProj_dvd _ _)]
    exact DFunLike.congr_fun (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.inverseMultiple_comp f hf) x
  have hi := TateKernelDeterminant.primary_tateMap_injective p h f g c u hu hgf
  intro hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hi)

theorem determinant_norm :
    ‖((AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det : ℚ_[p])‖ = ‖(Nat.card f.ker : ℚ_[p])‖ := by
  have hn : (Nat.card f.ker : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AlgebraicGeometry.AbelianScheme.TateComparison.FiniteKernelDivision.FiniteKernel.card_ne_zero f)
  rw [Padic.norm_eq_zpow_neg_valuation (PadicInt.coe_ne_zero.mpr
      (determinant_ne_zero p f hf hdiv)), Padic.norm_eq_zpow_neg_valuation hn,
    PadicInt.valuation_coe, Padic.valuation_natCast,
    determinant_valuation p f hf hdiv, Nat.factorization_def _ (Fact.out : p.Prime)]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TateFiniteKernelNorm
