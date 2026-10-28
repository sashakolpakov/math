import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheRow
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheSemantics

namespace OAI.Algorithms

/-! The concrete emitted row is the target-ring Lagrange basis polynomial.
The denominator condition of the actual inverse program is discharged here. -/

noncomputable section

namespace SubexponentialSAT.SubexpLagrangeCacheRowCorrectness

open Polynomial BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheState
open SubexpLagrangeCacheAlgebra SubexpLagrangeCacheSemantics

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def basis (i : Fin p) : Polynomial (SubexpActualRing.Ring p μ) :=
  TableInterpolation.basis (integerNodes p μ) (integerNodes_units p μ) i

def basisAt (i : ℕ) : Polynomial (SubexpActualRing.Ring p μ) :=
  if h : i < p then basis p μ ⟨i, h⟩ else 0

def Correct (row : List (Coefficient p μ)) (i : ℕ) : Prop :=
  row.length = p ∧ polyValue p μ (QuarticSearch.liftedCoefficients p μ) row = basisAt p μ i

theorem products_denominator (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (i : Fin p) :
    SubexpLagrangeInverseCall.denote p μ
      (SubexpLagrangeCacheRow.products p μ M p t zero one minusOne i.val).denominator =
        denominator (integerNodes p μ) i :=
  actual_run_denominator p μ M t zero one ht hz ho minusOne hm i

theorem row_value (t zero one : Coefficient p μ) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (i : Fin p) (inverse : Coefficient p μ)
    (hinv : SubexpLagrangeInverseCall.denote p μ inverse *
      SubexpLagrangeInverseCall.denote p μ
        (SubexpLagrangeCacheRow.products p μ M p t zero one minusOne i.val).denominator = 1) :
    polyValue p μ (QuarticSearch.liftedCoefficients p μ)
      (SubexpLagrangeCacheRow.row p μ M p t zero one minusOne i.val inverse) = basis p μ i := by
  let P := (SubexpLagrangeCacheRow.products p μ M p t zero one minusOne i.val).polynomial
  let Q := SubexpLocalCorrectionAlgebra.padded zero inverse zero p
  have hp : polyValue p μ (QuarticSearch.liftedCoefficients p μ) P =
      numerator (integerNodes p μ) i :=
    actual_run_numerator p μ M t zero one ht hz ho minusOne hm i
  have hq : polyValue p μ (QuarticSearch.liftedCoefficients p μ) Q =
      Truncation.trunc p (C (SubexpLagrangeInverseCall.denote p μ inverse)) := by
    have h := SubexpLocalCorrectionAlgebra.padded_denote
      (value p μ (QuarticSearch.liftedCoefficients p μ)) zero inverse zero hz p
    rw [show value p μ (QuarticSearch.liftedCoefficients p μ) zero = 0 from hz,
      map_zero, mul_zero, add_zero] at h
    exact h
  have hprod := SubexpTruncatedMultiply.result_correct p μ M
    (QuarticSearch.liftedCoefficients p μ) t zero ht hz p P Q
  change polyValue p μ (QuarticSearch.liftedCoefficients p μ)
      (SubexpLagrangeCacheRow.row p μ M p t zero one minusOne i.val inverse) =
    Truncation.trunc p
      (polyValue p μ (QuarticSearch.liftedCoefficients p μ) P *
        polyValue p μ (QuarticSearch.liftedCoefficients p μ) Q) at hprod
  rw [hp, hq] at hprod
  change (polyValue p μ (QuarticSearch.liftedCoefficients p μ)
      (SubexpLagrangeCacheRow.row p μ M p t zero one minusOne i.val inverse) :
        Polynomial (SubexpActualRing.Ring p μ)) =
    Truncation.trunc p
      ((numerator (integerNodes p μ) i : Polynomial (SubexpActualRing.Ring p μ)) *
        Truncation.trunc p
          (C (SubexpLagrangeInverseCall.denote p μ inverse) :
            Polynomial (SubexpActualRing.Ring p μ))) at hprod
  have hright := SubexpTruncatedGeometric.trunc_mul_trunc_right
    (R := SubexpActualRing.Ring p μ) p (numerator (integerNodes p μ) i)
      (C (SubexpLagrangeInverseCall.denote p μ inverse))
  have hcomm : Truncation.trunc p
      (numerator (integerNodes p μ) i * C (SubexpLagrangeInverseCall.denote p μ inverse)) =
    Truncation.trunc p
      (C (SubexpLagrangeInverseCall.denote p μ inverse) * numerator (integerNodes p μ) i) :=
    congrArg (Truncation.trunc p)
      (mul_comm (numerator (integerNodes p μ) i)
        (C (SubexpLagrangeInverseCall.denote p μ inverse)))
  have hprod' := hprod.trans (hright.trans hcomm)
  have htrunc : Truncation.trunc p
      (C (SubexpLagrangeInverseCall.denote p μ inverse) * numerator (integerNodes p μ) i) =
      C (SubexpLagrangeInverseCall.denote p μ inverse) * numerator (integerNodes p μ) i := by
    ext j
    by_cases hj : j < p
    · simp [Truncation.coeff_trunc, hj]
    · have hzj := numerator_coeff_eq_zero (Fact.out : p.Prime).pos (integerNodes p μ) i
        (Nat.le_of_not_gt hj)
      simp [Truncation.coeff_trunc, hj, coeff_C_mul, hzj]
  rw [htrunc] at hprod'
  rw [products_denominator p μ M t zero one minusOne ht hz ho hm i] at hinv
  exact hprod'.trans (actual_scaled_numerator_eq_basis p μ i _ hinv)

theorem command_correct (hμ : 0 < μ) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ)) (width exponent counter : List Bool)
    (s : Store) (i : Fin p)
    (H : SubexpLagrangeCacheRow.Environment p μ M p t zero one minusOne width exponent counter s i.val)
    (cache : List (List (List Bool)))
    (hcache : s 250 = Subexp.FactorPacketCoordinates.cacheBytes cache)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1)
    (he : BinaryArithmetic.toNat exponent = p ^ 4 - 2)
    (hc : CounterPrograms.value counter = μ) (regs : Fin 16 → Bool) :
    ∃ n rf r, n ≤ SubexpLagrangeCacheRow.budget p (baseWidth p μ) i.val exponent counter ∧
      Eval (SubexpLagrangeCacheControl.outerStep SubexpLagrangeInverseCall.command) n
        (⟨regs, s⟩ : Data)
        ⟨rf, SubexpLagrangeCacheRow.output p μ M s zero one i.val (r.map SubexpFlatAdd.encode) cache⟩ ∧
      Correct p μ r i.val := by
  have ha : SubexpActualRing.rho p μ hμ (SubexpLagrangeInverseCall.denote p μ
      (SubexpLagrangeCacheRow.products p μ M p t zero one minusOne i.val).denominator) ≠ 0 := by
    rw [products_denominator p μ M t zero one minusOne ht hz ho hm i]
    exact actual_denominator_rho_ne_zero p μ hμ i
  obtain ⟨n, rf, inverse, hn, hrun, hi, hlen⟩ :=
    SubexpLagrangeCacheRow.command_correct p μ M hμ p t zero one minusOne width exponent counter
      s i.val H cache hcache ht ho hm he hc ha regs
  refine ⟨n, rf, SubexpLagrangeCacheRow.row p μ M p t zero one minusOne i.val inverse,
    hn, hrun, hlen, ?_⟩
  simpa only [basisAt, dite_eq_left i.isLt] using row_value p μ M t zero one minusOne ht hz ho hm i inverse hi

end SubexponentialSAT.SubexpLagrangeCacheRowCorrectness

end

end OAI.Algorithms
