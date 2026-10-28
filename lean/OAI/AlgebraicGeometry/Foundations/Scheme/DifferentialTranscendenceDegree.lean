import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceEtale

/-! # Differential Transcendence Degree -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree

noncomputable section

/-!
# Differential dimension and transcendence bases

This module constructs actual bases of Kähler differential modules by base
change from polynomial rings. The field-theoretic hypotheses are used to
prove formal étaleness, rather than assuming a dimension formula.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.Module
open scoped TensorProduct

universe u

section EtalePolynomial

variable (k K ι : Type u) [Field k] [Field K] [Algebra k K]
variable [Algebra (MvPolynomial ι k) K] [IsScalarTower k (MvPolynomial ι k) K]
variable [Algebra.FormallyEtale (MvPolynomial ι k) K]

/-- A formally étale algebra over a polynomial ring has the base-changed
coordinate differentials as an actual basis of its differentials over k. -/
def kaehlerPolynomialEtaleBasis : Basis ι K Ω[K⁄k] :=
  ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) K)

/-- The dimension here follows from a constructed basis, not an assumed
geometric dimension or a surrogate differential object. -/
theorem kaehlerPolynomialEtale_rank : Module.rank K Ω[K⁄k] = Cardinal.mk ι :=
  (kaehlerPolynomialEtaleBasis k K ι).mk_eq_rank''.symm

/-- The basis vectors are the actual universal differentials of the images
of the polynomial coordinates. -/
theorem kaehlerPolynomialEtaleBasis_apply (i : ι) :
    kaehlerPolynomialEtaleBasis k K ι i =
      KaehlerDifferential.D k K (algebraMap (MvPolynomial ι k) K (MvPolynomial.X i)) := by
  simp [kaehlerPolynomialEtaleBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

/-- For an actual transcendence basis, the constructed differential basis
has cardinality equal to the standard transcendence degree. -/
theorem kaehler_rank_eq_trdeg_of_etale_polynomial {v : ι → K}
    (hv : IsTranscendenceBasis k v) :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K :=
  (kaehlerPolynomialEtale_rank k K ι).trans hv.cardinalMk_eq_trdeg

end EtalePolynomial

section FinitelyGeneratedFields

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable [PerfectField k] [Algebra.EssFiniteType k K]

/-- A finitely generated extension of a perfect field has a finite
transcendence basis whose cardinality also indexes a constructed basis of
its actual Kähler differential module. -/
theorem exists_transcendenceBasis_kaehlerBasis :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Nonempty (Basis s K Ω[K⁄k]) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hset : Set.range ((↑) : s → K) = (s : Set K) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  let : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rw [hset]
    exact hsep
  let : Algebra (MvPolynomial s k) K := TranscendenceEtale.polynomialEvaluationAlgebra k ((↑) : s → K)
  let : IsScalarTower k (MvPolynomial s k) K :=
    TranscendenceEtale.polynomialEvaluation_isScalarTower k ((↑) : s → K)
  let : Algebra.FormallyEtale (MvPolynomial s k) K :=
    TranscendenceEtale.formallyEtale_polynomialEvaluation hs.1
  exact ⟨s, hs, ⟨kaehlerPolynomialEtaleBasis k K s⟩⟩

/-- Differential rank equals the standard transcendence degree for a
finitely generated extension of a perfect field. -/
theorem kaehler_rank_eq_trdeg : Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  obtain ⟨s, hs, ⟨b⟩⟩ := exists_transcendenceBasis_kaehlerBasis k K
  exact b.mk_eq_rank''.symm.trans hs.cardinalMk_eq_trdeg

/-- The differential module in this theorem is finite-dimensional. -/
theorem kaehler_finite_of_essFiniteType : Module.Finite K Ω[K⁄k] := by
  obtain ⟨s, _, ⟨b⟩⟩ := exists_transcendenceBasis_kaehlerBasis k K
  exact Module.Finite.of_basis b

/-- The same dimension identity in natural-number form. -/
theorem kaehler_finrank_eq_trdeg :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  exact congrArg Cardinal.toNat (kaehler_rank_eq_trdeg k K)

end FinitelyGeneratedFields

variable (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

/-- In characteristic zero, a finitely generated field extension has
differential dimension equal to its transcendence degree, with no separate
separability or dimension assumption. -/
theorem kaehler_rank_eq_trdeg_charZero :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K :=
  kaehler_rank_eq_trdeg k K

/-- Natural-number differential dimension in characteristic zero. -/
theorem kaehler_finrank_eq_trdeg_charZero :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat :=
  kaehler_finrank_eq_trdeg k K

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree
