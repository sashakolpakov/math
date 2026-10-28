import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegers
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AdicTransport
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Evaluation Integers Henselian -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegersHenselian.Lifts

noncomputable section

/-!
The finite evaluation DVR is complete in its own maximal-ideal topology.
Finite freeness first gives completeness for the old maximal ideal, then
the artinian residue algebra supplies cofinality of the new ideal powers.
-/

universe u

variable (R K L : Type u) [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]

theorem evaluationIntegerRing_complete :
    letI := EvaluationIntegers.Lifts.evaluationIntegerRing_local R K L
    IsAdicComplete (IsLocalRing.maximalIdeal (EvaluationIntegers.Lifts.evaluationIntegerRing R L))
      (EvaluationIntegers.Lifts.evaluationIntegerRing R L) := by
  let A := EvaluationIntegers.Lifts.evaluationIntegerRing R L
  let := EvaluationIntegers.Lifts.evaluationIntegerRing_local R K L
  have : Module.Finite R A := EvaluationIntegers.Lifts.evaluationIntegerRing_finite R K L
  have : Module.Free R A := EvaluationIntegers.Lifts.evaluationIntegerRing_free R K L
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) A :=
    FiniteFreeCompletion.Lifts.finite_free_adic_complete R A (IsLocalRing.maximalIdeal R)
  let I : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  have : IsAdicComplete I A := (IsAdicComplete.map_algebraMap_iff
    (I := IsLocalRing.maximalIdeal R) (S := A) (M := A)).mpr inferInstance
  have hI : I ≤ IsLocalRing.maximalIdeal A :=
    (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R A).trans
      (sInf_le ⟨bot_le, IsLocalRing.maximalIdeal.isMaximal A⟩)
  let k := IsLocalRing.ResidueField R
  let Q := A ⧸ I
  let : Algebra k Q := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R k Q := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite k Q := Module.Finite.of_restrictScalars_finite R k Q
  have : IsArtinianRing Q := isArtinian_of_tower k inferInstance
  obtain ⟨e, he⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AdicTransport.Lifts.adic_complete_of_cofinal_powers I (IsLocalRing.maximalIdeal A) A hI e he

include K in
theorem evaluationIntegerRing_henselian : HenselianLocalRing (EvaluationIntegers.Lifts.evaluationIntegerRing R L) := by
  let := EvaluationIntegers.Lifts.evaluationIntegerRing_local R K L
  have := evaluationIntegerRing_complete R K L
  exact AdicTransport.Lifts.complete_local_henselian (EvaluationIntegers.Lifts.evaluationIntegerRing R L)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegersHenselian.Lifts
