import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegersHenselian

/-! # Evaluation DVR Lifts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts

noncomputable section

/-!
A constructed finite evaluation DVR, packaged with its fraction field,
completeness, henselianity, and the actual residue-ring identification.
Every field is supplied by the integral-closure construction proved above.
-/

universe u

structure EvaluationDVR (R L : Type u) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra R L] where
  carrier : Type u
  [ring : CommRing carrier]
  [domain : IsDomain carrier]
  [dvr : IsDiscreteValuationRing carrier]
  [henselian : HenselianLocalRing carrier]
  [complete : IsAdicComplete (IsLocalRing.maximalIdeal carrier) carrier]
  [algebra : Algebra R carrier]
  [algebraToField : Algebra carrier L]
  [scalarTower : IsScalarTower R carrier L]
  [fractionField : IsFractionRing carrier L]
  [finite : Module.Finite R carrier]
  residueIso : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField carrier
  residue_compatible : ∀ r : R, residueIso (IsLocalRing.residue R r) =
    IsLocalRing.residue carrier (algebraMap R carrier r)

attribute [instance] EvaluationDVR.ring EvaluationDVR.domain EvaluationDVR.dvr EvaluationDVR.henselian
  EvaluationDVR.complete EvaluationDVR.algebra EvaluationDVR.algebraToField EvaluationDVR.scalarTower
  EvaluationDVR.fractionField EvaluationDVR.finite

variable (R K L : Type u) [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable [IsAlgClosed (IsLocalRing.ResidueField R)]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]

/-- The finite field used to evaluate all generic parameters has an
actual complete henselian DVR of integers with the original residue field. -/
def evaluationDVR : EvaluationDVR R L := by
  let A := EvaluationIntegers.Lifts.evaluationIntegerRing R L
  letI : IsDiscreteValuationRing A := EvaluationIntegers.Lifts.evaluationIntegerRing_dvr R K L
  letI : HenselianLocalRing A := EvaluationIntegersHenselian.Lifts.evaluationIntegerRing_henselian R K L
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := EvaluationIntegersHenselian.Lifts.evaluationIntegerRing_complete R K L
  letI : Module.Finite R A := EvaluationIntegers.Lifts.evaluationIntegerRing_finite R K L
  letI : IsFractionRing A L := EvaluationIntegers.Lifts.evaluationIntegerRing_fractionField R K L
  exact {
    carrier := A
    residueIso := EvaluationIntegers.Lifts.evaluationIntegerResidueIso R K L
    residue_compatible := EvaluationIntegers.Lifts.evaluationIntegerResidueIso_comp R K L }

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts
