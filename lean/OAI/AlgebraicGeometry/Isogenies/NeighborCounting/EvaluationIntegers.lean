import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteLocalExtension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Evaluation Integers -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegers.Lifts

noncomputable section

/-!
The integral closure in a finite separable evaluation field is a finite
local DVR with that field of fractions. When the original residue field
is algebraically closed, the residue extension is canonically trivial.
-/

universe u

variable (R K L : Type u) [CommRing R] [IsDomain R]
variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]

abbrev evaluationIntegerRing := integralClosure R L

include K in
omit [HenselianLocalRing R] in
theorem evaluationIntegerRing_finite : Module.Finite R (evaluationIntegerRing R L) :=
  IsIntegralClosure.finite R K L (integralClosure R L)

include K in
theorem evaluationIntegerRing_local : IsLocalRing (evaluationIntegerRing R L) := by
  have := evaluationIntegerRing_finite R K L
  exact FiniteLocalExtension.Lifts.finite_domain_isLocalRing R (integralClosure R L)

include K in
omit [IsDiscreteValuationRing R] [HenselianLocalRing R] [Algebra.IsSeparable K L] in
theorem evaluationIntegerRing_fractionField : IsFractionRing (evaluationIntegerRing R L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension R K L (integralClosure R L)

include K in
omit [HenselianLocalRing R] in
theorem evaluationIntegerRing_dedekind : IsDedekindDomain (evaluationIntegerRing R L) :=
  integralClosure.isDedekindDomain R K L

include K in
omit [HenselianLocalRing R] in
theorem evaluationIntegerRing_free : Module.Free R (evaluationIntegerRing R L) := by
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  exact IsIntegralClosure.module_free R K L (integralClosure R L)

include K in
omit [HenselianLocalRing R] [Module.Finite K L] [Algebra.IsSeparable K L] in
theorem evaluationIntegerRing_not_isField : ¬ IsField (evaluationIntegerRing R L) := by
  intro h
  apply IsDiscreteValuationRing.not_isField (R := R)
  apply isField_of_isIntegral_of_isField (S := integralClosure R L) _ h
  intro x y he
  have hL : algebraMap R L x = algebraMap R L y := congrArg Subtype.val he
  rw [IsScalarTower.algebraMap_eq R K L] at hL
  exact (IsFractionRing.injective R K) ((algebraMap K L).injective hL)

include K in
theorem evaluationIntegerRing_dvr : IsDiscreteValuationRing (evaluationIntegerRing R L) := by
  have := evaluationIntegerRing_dedekind R K L
  have := evaluationIntegerRing_local R K L
  exact ((IsDiscreteValuationRing.TFAE (evaluationIntegerRing R L)
    (evaluationIntegerRing_not_isField R K L)).out 1 3).mpr
      (evaluationIntegerRing_dedekind R K L)

include K in
/-- The evaluation extension has a constructed finite DVR of integers,
with no locality or discrete-valuation assumption on that integral closure. -/
theorem evaluationIntegerRing_geometry :
    Module.Finite R (evaluationIntegerRing R L) ∧
      Module.Free R (evaluationIntegerRing R L) ∧
      IsDiscreteValuationRing (evaluationIntegerRing R L) ∧
      IsFractionRing (evaluationIntegerRing R L) L :=
  ⟨evaluationIntegerRing_finite R K L, evaluationIntegerRing_free R K L,
    evaluationIntegerRing_dvr R K L, evaluationIntegerRing_fractionField R K L⟩

variable [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- The residue extension is the actual residue map of the finite local
extension; algebraic closedness proves that it is an isomorphism. -/
def evaluationIntegerResidueIso :
    letI := evaluationIntegerRing_local R K L
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField (evaluationIntegerRing R L) := by
  letI := evaluationIntegerRing_local R K L
  have := evaluationIntegerRing_finite R K L
  exact RingEquiv.ofBijective
    (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (evaluationIntegerRing R L)))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem evaluationIntegerResidueIso_comp (r : R) :
    letI := evaluationIntegerRing_local R K L
    evaluationIntegerResidueIso R K L (IsLocalRing.residue R r) =
      IsLocalRing.residue (evaluationIntegerRing R L)
        (algebraMap R (evaluationIntegerRing R L) r) := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationIntegers.Lifts
