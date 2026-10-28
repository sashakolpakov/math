import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger
import OAI.RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction

/-! # Prime Intertwiner -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeIntertwiner.CM

/-! Every actual local oscillator extends to an exact global Heisenberg
intertwiner. Only the already constructed character is used. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeHeisenberg.CM
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem away_mem (p s : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))
    (f : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    PrimeHeisenberg.CM.awayHeisenbergFunction q p s f.val ∈ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) := by
  constructor
  · apply IsLocallyConstant.mul
    · apply Constructed.AdelicCharacter.CM.Finite.character_locallyConstant.comp_continuous
      unfold dotProduct
      fun_prop
    · exact f.property.1.comp_continuous (continuous_id.sub continuous_const)
  · exact (f.property.2.comp_homeomorph (Homeomorph.subRight s)).mul_left

def awayOperator (p s : RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) :
    RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) →ₗ[ℂ]
      RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n)) where
  toFun f := ⟨PrimeHeisenberg.CM.awayHeisenbergFunction q p s f.val, away_mem q n p s f⟩
  map_add' f h := by apply Subtype.ext; funext x; exact mul_add _ _ _
  map_smul' c f := by apply Subtype.ext; funext x; exact mul_left_comm _ _ _

theorem heisenberg_tensor (p s : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (h : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.FullPrimeAwayPosition q (ι := Fin n))) :
    Finite.FourierHeisenberg.CM.operator p s (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n
        (LocalTestCommutant.CM.Prime.localHeisenberg q n
          (Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q s) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q p)) f)
        (awayOperator q n (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q s) h) := by
  apply Subtype.ext
  funext x
  have hfun : (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h).val =
      fun z => f.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q z) * h.val (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q z) :=
    funext (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply q n f h)
  rw [Finite.FourierHeisenberg.CM.operator_apply, hfun, PrimeHeisenberg.CM.fullPrime_heisenberg_function,
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply, RepresentationTheory.Hecke.RadialDilation.PrimeHeisenberg.Realization.padic_heisenberg_coordinate_convention]
  rfl

theorem local_covariance (u : Local.Schrodinger.CM.LocalOscillator q n)
    (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    u.val.2 (LocalTestCommutant.CM.Prime.localHeisenberg q n v f) =
      LocalTestCommutant.CM.Prime.localHeisenberg q n (u.val.1.val *ᵥ v) (u.val.2 f) := by
  apply Subtype.ext
  exact (u.property.2 v f (LocalTestCommutant.CM.Prime.localHeisenberg q n v f)).mp rfl

theorem operator_covariance (u : Local.Schrodinger.CM.LocalOscillator q n) (p s : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2).toLinearMap.comp (Finite.FourierHeisenberg.CM.operator p s) =
      (Finite.FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrimeMomentum q n u.val.1 p s)
        (RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrimePosition q n u.val.1 p s)).comp (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2).toLinearMap := by
  apply RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_linear_ext q n
  intro f h
  change RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2 (Finite.FourierHeisenberg.CM.operator p s (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h)) =
    Finite.FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrimeMomentum q n u.val.1 p s) (RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrimePosition q n u.val.1 p s)
      (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2 (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h))
  rw [heisenberg_tensor, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_tensor, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_tensor,
    heisenberg_tensor, RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrime_transformed_away_momentum, RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrime_transformed_away_position,
    RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization.fullPrime_transformed_localPhase, local_covariance]

theorem intertwines (u : Local.Schrodinger.CM.LocalOscillator q n) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n))
      (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom u.val.1)) (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2) := by
  intro p s f h hh x
  have he : h = Finite.FourierHeisenberg.CM.operator p s f := Subtype.ext (funext hh)
  rw [he]
  exact congrArg (fun a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) => a.val x)
    (LinearMap.congr_fun (operator_covariance q n u p s) f)

theorem commutes_local_of_matrix_one (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n))
    (hU : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) g U)
    (hg : g.val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q) = 1)
    (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    U (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T f) = RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (U f) := by
  apply LocalTestCommutant.CM.Prime.commutes_all_local q n U.toLinearMap _ T f
  intro v a
  let p := fun i => v (Sum.inr i)
  let s := fun i => v (Sum.inl i)
  have hv : v = Sum.elim s p := by funext i; cases i <;> rfl
  rw [hv, PrimeHeisenberg.CM.local_operator]
  apply Subtype.ext
  funext x
  have h := hU (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) a
    (Finite.FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) a) (fun _ => rfl) x
  have he : Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) =
      RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q (Sum.elim p s) := by funext i; cases i <;> rfl
  have hfix : g.val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) =
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q p) (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q s) := by
    rw [he, RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction.Realization.fullPrime_matrix_inclusion, hg, Matrix.one_mulVec]
  rw [hfix] at h
  exact h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeIntertwiner.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeIntertwiner.CM.OperatorCommutation

/-! Operators obtained from local oscillators at distinct primes commute
on the actual global finite Schwartz space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization
variable (q p n : ℕ) [Fact q.Prime] [Fact p.Prime]

local instance (r : ℕ) [Fact r.Prime] : MeasurableSpace ℚ_[r] := borel ℚ_[r]
local instance (r : ℕ) [Fact r.Prime] : BorelSpace ℚ_[r] := ⟨rfl⟩

theorem rationalPrime_ne (hpq : p ≠ q) : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p ≠ RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q := by
  intro h
  have he := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective h
  exact hpq (congrArg Subtype.val he)

theorem included_matrix_other (hpq : p ≠ q) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) :
    (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q g).val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p) = 1 := by
  change (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePrimeMatrix (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) (g.val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q))).map
    ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm ∘ RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p)) = 1
  rw [← Matrix.map_map, RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePrimeMatrix_eval_other (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p)
    (rationalPrime_ne q p hpq)]
  exact (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm.toRingHom.mapMatrix.map_one

theorem oscillator_commutes_operator (hpq : p ≠ q)
    (u : Local.Schrodinger.CM.LocalOscillator q n)
    (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[p] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[p] n) :
    Commute (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2) (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom p n T) := by
  apply LinearEquiv.ext
  intro f
  exact commutes_local_of_matrix_one p n
    (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom u.val.1))
    (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n u.val.2) (intertwines q n u)
    (included_matrix_other q p n hpq _) T f

theorem bare_operators_commute (hpq : p ≠ q)
    (u : Local.Schrodinger.CM.LocalMetaplectic q n)
    (v : Local.Schrodinger.CM.LocalMetaplectic p n) :
    Commute
      (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) u))
      (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom p n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[p] n (PadicCharacter.CM.character p) v)) :=
  oscillator_commutes_operator q p n hpq u.val _

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeIntertwiner.CM.OperatorCommutation

end

end OAI
