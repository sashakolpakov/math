import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt
import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction

/-! # Prime Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeHeisenberg.CM

noncomputable section

/-! Exact comparison of the actual local and global Heisenberg
operators. No WeilData or operator-matching hypothesis is used. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction.Realization
variable (q : ℕ) [Fact q.Prime] {ι : Type*} [Fintype ι]

def awayHeisenbergFunction
    (p s : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι))
    (f : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι) → ℂ) (y : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι)) : ℂ :=
  Constructed.AdelicCharacter.CM.Finite.character (p.val ⬝ᵥ (y.val - (1 / 2 : ℚ) • s.val)) * f (y - s)

theorem fullPrime_heisenberg_function
    (p s x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : (ι → ℚ_[q]) → ℂ) (h : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character p s
      (fun z => f (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q z) * h (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q z)) x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg (PadicCharacter.CM.character q) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q s)
        f (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x) *
      awayHeisenbergFunction q (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q s) h (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x) := by
  have hrat (u t : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
      (fun i => u i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * t i) = u - (1 / 2 : ℚ) • t := by
    funext i
    rw [Algebra.smul_def]
    rfl
  have hlocal (u t : ι → ℚ_[q]) :
      (fun i => u i - algebraMap ℚ ℚ_[q] (1 / 2) * t i) = u - (1 / 2 : ℚ) • t := by
    funext i
    rw [Algebra.smul_def]
    rfl
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg awayHeisenbergFunction
  change Constructed.AdelicCharacter.CM.Finite.character (p ⬝ᵥ (fun i => x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * s i)) *
    (f (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q (x - s)) * h (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q (x - s))) =
    (PadicCharacter.CM.character q (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q p ⬝ᵥ
      (fun i => RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x i - algebraMap ℚ ℚ_[q] (1 / 2) * RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q s i)) *
      f (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x - RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q s)) *
    (Constructed.AdelicCharacter.CM.Finite.character ((RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q p).val ⬝ᵥ
      ((RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val - (1 / 2 : ℚ) • (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q s).val)) *
      h (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x - RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q s))
  rw [hrat, hlocal, RepresentationTheory.Hecke.RadialDilation.PrimePairing.Realization.fullPrime_midpoint_pairing q, Constructed.AdelicCharacter.CM.Finite.character.map_add_eq_mul, map_sub, map_sub]
  change (PadicCharacter.CM.character q _ * Constructed.AdelicCharacter.CM.Finite.character _) * (_ * _) = _
  ring

theorem away_zero (h : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι) → ℂ) (y : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := ι)) :
    awayHeisenbergFunction q 0 0 h y = h y := by
  simp [awayHeisenbergFunction]

variable (n : ℕ)

theorem local_tensor (p s : Fin n → ℚ_[q]) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    Finite.FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p) f) h := by
  apply Subtype.ext
  funext x
  have hfun : (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h).val =
      fun z => f.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q z) * h.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q z) :=
    funext (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply q n f h)
  rw [Finite.FourierHeisenberg.CM.operator_apply, hfun, fullPrime_heisenberg_function,
    RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection_inclusion, RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection_inclusion,
    RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway_inclusion, RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway_inclusion, away_zero, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply,
    RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg.Realization.padic_heisenberg_coordinate_convention]
  rfl

theorem local_operator (p s : Fin n → ℚ_[q]) :
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p)) =
      Finite.FourierHeisenberg.CM.equivalence (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) := by
  apply LinearEquiv.toLinearMap_injective
  apply RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_linear_ext q n
  intro f h
  change RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p))
      (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h) =
    Finite.FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h)
  rw [RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_tensor, local_tensor]

theorem commutes_all_of_fixed_phase (g : Finite.FiniteOscillator.CM.Oscillator (I := Fin n))
    (hg : ∀ p s : Fin n → ℚ_[q],
      Finite.FiniteOscillator.CM.phaseAction (Finite.FiniteOscillator.CM.projection g)
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s))
    (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    Finite.FiniteOscillator.CM.action g (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T f) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (Finite.FiniteOscillator.CM.action g f) := by
  apply LocalTestCommutant.CM.Prime.commutes_all_local q n (Finite.FiniteOscillator.CM.action g).toLinearMap _ T f
  intro v a
  have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
    funext i
    cases i <;> rfl
  rw [hv, local_operator]
  exact Finite.PlaceAt.CM.CyclicVacuum.action_heisenberg_of_fixed g _ _ (hg _ _) a

theorem commutes_all_of_local_matrix_one (g : Finite.FiniteOscillator.CM.Oscillator (I := Fin n))
    (hg : (Finite.FiniteOscillator.CM.projection g).val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) = 1)
    (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    Finite.FiniteOscillator.CM.action g (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T f) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (Finite.FiniteOscillator.CM.action g f) := by
  apply commutes_all_of_fixed_phase q n g _ T f
  intro p s
  have he : Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) =
      RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q (Sum.elim p s) := by
    funext i
    cases i <;> rfl
  change (Finite.FiniteOscillator.CM.projection g).val *ᵥ _ = _
  rw [he, RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction.Realization.fullPrime_matrix_inclusion, hg, Matrix.one_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeHeisenberg.CM
