import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Schrodinger

/-! # Prime Quadratic -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM

/-! The quadratic operator supported at one prime is exactly the
extension of the proved local bare quadratic operator. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

def coefficients (B : Matrix (Fin n) (Fin n) ℚ_[q]) : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (B i j)

theorem coefficients_symmetric (B : Matrix (Fin n) (Fin n) ℚ_[q]) (hB : B.IsSymm) :
    (coefficients q n B).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q) (hB.apply i j)

theorem coefficients_mulVec (B : Matrix (Fin n) (Fin n) ℚ_[q]) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    coefficients q n B *ᵥ x = RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q (B *ᵥ RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x) := by
  funext i
  change (∑ j, RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (B i j) * x j) =
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (∑ j, B i j * RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (x j))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finitePadicInclusion_mul q (B i j) (x j))

theorem quadratic_formula (B : Matrix (Fin n) (Fin n) ℚ_[q]) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (coefficients q n B) x =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.quadratic B (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x)) := by
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic, coefficients_mulVec, dotProduct_comm x, RepresentationTheory.Hecke.RadialDilation.PrimePairing.Realization.fullPrime_pairing_local,
    RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.finitePadic_mul_inclusion]
  apply congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q)
  rw [(RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).commutes, RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction.quadratic_eq_dot]
  change algebraMap ℚ ℚ_[q] (1 / 2) * ((B *ᵥ RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x) ⬝ᵥ RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x) =
    (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x ⬝ᵥ (B *ᵥ RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeProjection q x)) / 2
  rw [dotProduct_comm]
  simp [div_eq_mul_inv, mul_comm]

theorem quadratic_operator (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) :
    Finite.Quadratic.CM.finiteQuadratic (coefficients q n B.val) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q)
        (Local.Schrodinger.CM.quadratic q n B)) := by
  apply LinearEquiv.toLinearMap_injective
  apply RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_linear_ext q n
  intro f h
  change Finite.Quadratic.CM.finiteQuadratic (coefficients q n B.val) (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h) =
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n _ (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor q n f h)
  rw [RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_tensor]
  apply Subtype.ext
  funext x
  rw [Finite.Quadratic.CM.finiteQuadratic_apply, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeTensor_apply,
    Local.Schrodinger.CM.quadratic_apply, quadratic_formula]
  rw [← PadicCharacter.CM.character_apply, mul_assoc]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM.FourierComparison

/-! Global and local Fourier conjugation agree on operators supported
at one prime. The proof uses exact Heisenberg covariance and the local
commutant, without a Fourier product or scalar-matching hypothesis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LocalTestCommutant.CM.Prime
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

def localFourier : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n :=
  (Local.Schrodinger.CM.fourier q n).val.2

def extendedFourier : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) :=
  RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (localFourier q n)

theorem local_covariance (p s : Fin n → ℚ_[q]) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    localFourier q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p) f) =
      LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim p (-s)) (localFourier q n f) := by
  have h := ((Local.Schrodinger.CM.fourier q n).property.2 (Sum.elim s p) f
    (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p) f)).mp rfl
  have hw : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic ℚ_[q] n) (Sum.elim s p) = Sum.elim p (-s) := by
    change (RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic ℚ_[q] n).val *ᵥ Sum.elim s p = _
    rw [RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic_matrix, Matrix.fromBlocks_mulVec]
    simp [Function.comp_def, Matrix.neg_mulVec]
  change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph (PadicCharacter.CM.character q)
    (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic ℚ_[q] n) (Sum.elim s p))
    (localFourier q n f) (localFourier q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p) f)) at h
  rw [hw] at h
  exact Subtype.ext h

theorem extended_covariance (p s : Fin n → ℚ_[q]) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    extendedFourier q n (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p)) f) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim p (-s))) (extendedFourier q n f) := by
  have he : localFourier q n * LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p) =
      LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim p (-s)) * localFourier q n := by
    apply LinearEquiv.ext
    exact local_covariance q n p s
  have hh := congrArg (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n) he
  rw [map_mul, map_mul] at hh
  exact congrArg (fun T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) => T f) hh

theorem global_covariance (p s : Fin n → ℚ_[q]) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    Finite.FourierHeisenberg.CM.Equiv.fourierEquiv
        (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim s p)) f) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n (Sum.elim p (-s)))
        (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv f) := by
  rw [PrimeHeisenberg.CM.local_operator, PrimeHeisenberg.CM.local_operator, map_neg]
  apply Subtype.ext
  funext x
  exact Finite.FourierHeisenberg.CM.fourier_heisenberg _ _ f.val x

def relative : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) :=
  (extendedFourier q n)⁻¹ * Finite.FourierHeisenberg.CM.Equiv.fourierEquiv

theorem relative_commutes (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    relative q n (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T f) = RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T (relative q n f) := by
  apply LocalTestCommutant.CM.Prime.commutes_all_local q n (relative q n).toLinearMap _ T f
  intro v a
  have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
    funext i
    cases i <;> rfl
  rw [hv]
  apply (extendedFourier q n).injective
  change extendedFourier q n ((extendedFourier q n).symm
      (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv
        (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n _) a))) =
    extendedFourier q n (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n (LocalTestCommutant.CM.Prime.localHeisenberg q n _)
      ((extendedFourier q n).symm (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv a)))
  rw [LinearEquiv.apply_symm_apply, global_covariance, extended_covariance,
    LinearEquiv.apply_symm_apply]

theorem conjugation_of_relative_commutes {G : Type*} [Group G] (L W U : G)
    (h : Commute (L⁻¹ * W) (L⁻¹ * U * L)) : W⁻¹ * U * W = L⁻¹ * U * L := by
  have he : W⁻¹ * U * W = (L⁻¹ * W)⁻¹ * (L⁻¹ * U * L) * (L⁻¹ * W) := by group
  rw [he, h.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]

theorem fourier_conjugation (T : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))⁻¹ * RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T *
      Finite.FourierHeisenberg.CM.Equiv.fourierEquiv =
    RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n ((localFourier q n)⁻¹ * T * localFourier q n) := by
  have he : RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n ((localFourier q n)⁻¹ * T * localFourier q n) =
      (extendedFourier q n)⁻¹ * RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n T * extendedFourier q n := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [he]
  apply conjugation_of_relative_commutes
  change Commute (relative q n) _
  rw [← he]
  apply LinearEquiv.ext
  exact relative_commutes q n _

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM.FourierComparison

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM.Lower

/-! The lower operator supported at one prime is the extension of an
actual local bare operator, obtained by Fourier conjugation. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM.FourierComparison
variable (q n : ℕ) [Fact q.Prime]

local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

def conjugateQuadratic (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) : Local.Schrodinger.CM.LocalMetaplectic q n := by
  let u := Local.Schrodinger.CM.quadratic q n ⟨-B.val, B.property.neg⟩
  let w := Local.Schrodinger.CM.fourier q n
  refine ⟨w⁻¹ * u.val * w, ?_⟩
  have h := (inferInstance : (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticSubgroup ℚ_[q] n (PadicCharacter.CM.character q)).Normal).conj_mem
    u.val u.property w⁻¹
  simpa only [inv_inv] using h

theorem conjugateQuadratic_action (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) (conjugateQuadratic q n B) =
      (FourierComparison.localFourier q n)⁻¹ *
        RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q)
          (Local.Schrodinger.CM.quadratic q n ⟨-B.val, B.property.neg⟩) * FourierComparison.localFourier q n := rfl

theorem conjugateQuadratic_projection (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (PadicCharacter.CM.character q) (conjugateQuadratic q n B) =
      RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B := by
  change RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℚ_[q] n (PadicCharacter.CM.character q)
    ((Local.Schrodinger.CM.fourier q n)⁻¹ *
      (Local.Schrodinger.CM.quadratic q n ⟨-B.val, B.property.neg⟩).val *
        Local.Schrodinger.CM.fourier q n) = _
  rw [map_mul, map_mul, map_inv]
  exact (RepresentationTheory.Weil.Local.OscillatorProjection.Construction.upper_quadratic_conjugation ℚ_[q] n B).symm

theorem coefficients_neg (B : Matrix (Fin n) (Fin n) ℚ_[q]) :
    coefficients q n (-B) = -coefficients q n B := by
  apply Matrix.ext
  intro i j
  exact map_neg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q) (B i j)

theorem lower_operator (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) :
    Finite.BareNe.CM.Group.bareAction
      (Finite.IntegralVacuum.CM.LowerBare.lowerLift (coefficients q n B.val) (coefficients_symmetric q n B.val B.property)) =
      RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom q n
        (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (PadicCharacter.CM.character q) (conjugateQuadratic q n B)) := by
  change (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))⁻¹ *
    Finite.Quadratic.CM.finiteQuadratic (-coefficients q n B.val) *
      Finite.FourierHeisenberg.CM.Equiv.fourierEquiv = _
  rw [← coefficients_neg q n B.val, quadratic_operator q n ⟨-B.val, B.property.neg⟩,
    FourierComparison.fourier_conjugation, conjugateQuadratic_action]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeQuadratic.CM.Lower

end

end OAI
