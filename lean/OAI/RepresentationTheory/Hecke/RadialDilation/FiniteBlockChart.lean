import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitLinearTopology
import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Finite Block Chart -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization

noncomputable section

section

/-! The actual split-place chart for one three-dimensional position block. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} (μ : Place)

def finiteBlockProjection : (Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[ℚ] Mem.Realization.Position q :=
  LinearMap.pi (fun i => (FiniteSchur.Realization.finitePadicProjection q).toLinearMap.comp (LinearMap.proj (μ, i)))

def finiteBlockInclusion : Mem.Realization.Position q →ₗ[ℚ] (Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :=
  LinearMap.pi (fun p => if p.1 = μ then
    (FiniteSchur.Realization.finitePadicInclusion q).comp (LinearMap.proj p.2) else 0)

theorem finiteBlockProjection_inclusion (x : Mem.Realization.Position q) :
    finiteBlockProjection q μ (finiteBlockInclusion q μ x) = x := by
  funext i
  simp [finiteBlockProjection, finiteBlockInclusion, FiniteSchur.Realization.finitePadicProjection_inclusion]

theorem finiteBlockProjection_continuous : Continuous (finiteBlockProjection q μ) := by
  apply continuous_pi
  intro i
  exact (FiniteSchur.Realization.finitePadicProjection_continuous q).comp (continuous_apply (μ, i))

theorem finiteBlockInclusion_continuous : Continuous (finiteBlockInclusion q μ) := by
  apply continuous_pi
  intro p
  dsimp only [finiteBlockInclusion, LinearMap.pi_apply]
  by_cases hp : p.1 = μ
  · simp only [hp, ite_true, LinearMap.comp_apply, LinearMap.proj_apply]
    exact (FiniteSchur.Realization.finitePadicInclusion_continuous q).comp (continuous_apply p.2)
  · simp only [hp, ite_false, LinearMap.zero_apply]
    exact continuous_const

abbrev FiniteAwayPosition := LinearMap.ker (finiteBlockProjection q μ)

/-- Split the chosen q-adic block from all remaining finite-adelic coordinates. -/
def finiteBlockChart : (Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × FiniteAwayPosition q μ :=
  SplitLinearTopology.Realization.splitLinearHomeomorph (finiteBlockProjection q μ) (finiteBlockInclusion q μ)
    (finiteBlockProjection_inclusion q μ)
    (finiteBlockProjection_continuous q μ) (finiteBlockInclusion_continuous q μ)

theorem finiteBlockChart_fst (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (finiteBlockChart q μ x).1 = finiteBlockProjection q μ x := rfl

theorem finiteBlockChart_symm (x : Mem.Realization.Position q) (y : FiniteAwayPosition q μ) :
    (finiteBlockChart q μ).symm (x, y) = finiteBlockInclusion q μ x + y.val := rfl

end

/-! Multiplicative orthogonality of the chosen p-adic coordinate and its complement. -/

open scoped Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem finitePrimeInclude_mul (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) (a : Theta.PoissonAutomorphyNormalizationData.AQf) :
    FiniteSchur.Realization.finitePrimeInclude v x * a = FiniteSchur.Realization.finitePrimeInclude v (x * FiniteSchur.Realization.finitePrimeEval v a) := by
  apply DFunLike.ext
  intro w
  change RestrictedProduct.single (fun z : HeightOneSpectrum ℤ => z.adicCompletionIntegers ℚ) v x w * a w =
    RestrictedProduct.single (fun z : HeightOneSpectrum ℤ => z.adicCompletionIntegers ℚ) v (x * a v) w
  by_cases hw : w = v
  · subst w
    rw [RestrictedProduct.single_eq_same, RestrictedProduct.single_eq_same]
  · rw [RestrictedProduct.single_eq_of_ne _ _ hw, RestrictedProduct.single_eq_of_ne _ _ hw, zero_mul]

variable (q : ℕ) [Fact q.Prime]

theorem finitePadicInclusion_mul (x : ℚ_[q]) (a : Theta.PoissonAutomorphyNormalizationData.AQf) :
    FiniteSchur.Realization.finitePadicInclusion q x * a = FiniteSchur.Realization.finitePadicInclusion q (x * FiniteSchur.Realization.finitePadicProjection q a) := by
  change FiniteSchur.Realization.finitePrimeInclude (FiniteSchur.Realization.rationalPrime q) (FiniteSchur.Realization.padicCoordinateEquiv q x) * a =
    FiniteSchur.Realization.finitePrimeInclude (FiniteSchur.Realization.rationalPrime q)
      (FiniteSchur.Realization.padicCoordinateEquiv q (x * (FiniteSchur.Realization.padicCoordinateEquiv q).symm (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) a)))
  rw [map_mul, ContinuousAlgEquiv.apply_symm_apply, finitePrimeInclude_mul]

variable {Place : Type*} (μ : Place)

theorem finiteBlockInclusion_apply (x : Mem.Realization.Position q) (p : Place × Fin 3) :
    finiteBlockInclusion q μ x p = if p.1 = μ then FiniteSchur.Realization.finitePadicInclusion q (x p.2) else 0 := by
  simp only [finiteBlockInclusion, LinearMap.pi_apply]
  split_ifs <;> rfl

variable [Fintype Place]

theorem finiteBlock_pairing (p : Mem.Realization.Position q) (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    ∑ j, finiteBlockInclusion q μ p j * x j =
      FiniteSchur.Realization.finitePadicInclusion q (∑ i, p i * finiteBlockProjection q μ x i) := by
  rw [Fintype.sum_prod_type]
  simp only [finiteBlockInclusion_apply]
  have hsum (v : Place) :
      (∑ i : Fin 3, (if v = μ then FiniteSchur.Realization.finitePadicInclusion q (p i) else 0) * x (v, i)) =
        if v = μ then ∑ i, FiniteSchur.Realization.finitePadicInclusion q (p i) * x (v, i) else 0 := by
    split_ifs <;> simp
  simp_rw [hsum]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ μ), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact finitePadicInclusion_mul q (p i) (x (μ, i))

theorem finiteBlock_pairing_away (p : Mem.Realization.Position q) (x : FiniteAwayPosition q μ) :
    ∑ j, finiteBlockInclusion q μ p j * x.val j = 0 := by
  rw [finiteBlock_pairing]
  have hx : finiteBlockProjection q μ x.val = 0 := x.property
  rw [hx]
  simp

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization
