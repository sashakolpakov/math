import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramQuotient
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

/-- A ternary residue has a constant-size literal encoding. -/
def ternaryLiteral (a : ZMod 3) : List Bool :=
  if a.val = 0 then [] else if a.val = 1 then [true] else [false, true]

@[simp] theorem ternaryLiteral_value (a : ZMod 3) : BinaryArithmetic.toNat (ternaryLiteral a) = a.val := by
  have ha := a.val_lt
  interval_cases h : a.val <;> simp [ternaryLiteral, h, BinaryArithmetic.toNat, bitVal]

@[simp] theorem ternaryLiteral_length (a : ZMod 3) : (ternaryLiteral a).length ≤ 2 := by
  unfold ternaryLiteral
  split <;> simp_all
  split <;> simp

def liftCoefficientRun (t : ℕ) (a : ZMod 3) : ScalarCode 3 t × ℕ :=
  SubexponentialSAT.SubexpPreparedQuartic.literalWordRun 3 t (ternaryLiteral a)

theorem liftCoefficientRun_value (t : ℕ) (ht : 0 < t) (a : ZMod 3) :
    BinaryArithmetic.toNat (liftCoefficientRun t a).1.val = a.val := by
  change BinaryArithmetic.toNat (SubexponentialSAT.SubexpModulusConstruction.normalizeRun _ _).1 = _
  rw [SubexponentialSAT.SubexpModulusConstruction.normalizeRun_value, ternaryLiteral_value]
  rw [ternaryLiteral_value, ternary_baseWidth]
  have hpow : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by omega) (by omega)
  have ha := a.val_lt
  norm_num at hpow
  omega

theorem liftCoefficientRun_canonical (t : ℕ) (ht : 0 < t) (a : ZMod 3) :
    BinaryArithmetic.toNat (liftCoefficientRun t a).1.val < 3^t := by
  rw [liftCoefficientRun_value t ht]
  have hpow : 3^1 ≤ 3^t := Nat.pow_le_pow_right (by omega) ht
  exact a.val_lt.trans_le (by simpa using hpow)

theorem liftCoefficientRun_correct (t : ℕ) (ht : 0 < t) (a : ZMod 3) :
    wordValue 3 t (liftCoefficientRun t a).1 = (a.val : ZMod (3^t)) := by
  unfold wordValue
  rw [liftCoefficientRun_value t ht]

@[simp] theorem liftCoefficientRun_cost (t : ℕ) (a : ZMod 3) :
    (liftCoefficientRun t a).2 = 3 * baseWidth 3 t + 1 :=
  SubexponentialSAT.SubexpPreparedQuartic.literalWordRun_cost 3 t _

/-- Materialized coefficient words for the lower coefficients of the monic
polynomial. The leading coefficient is implicit. -/
def liftCoefficientsRun (t : ℕ) {d : ℕ} (a : Fin d → ZMod 3) :
    Code (ScalarCode 3 t) d × ℕ := tabulateRun fun i => liftCoefficientRun t (a i)

@[simp] theorem liftCoefficientsRun_correct (t : ℕ) (ht : 0 < t) {d : ℕ}
    (a : Fin d → ZMod 3) (i : Fin d) :
    wordValue 3 t ((liftCoefficientsRun t a).1 i) = ((a i).val : ZMod (3^t)) := by
  simp only [liftCoefficientsRun, tabulateRun_eq]
  exact liftCoefficientRun_correct t ht (a i)

@[simp] theorem liftCoefficientsRun_cost (t : ℕ) {d : ℕ} (a : Fin d → ZMod 3) :
    (liftCoefficientsRun t a).2 = d * (3 * baseWidth 3 t + 1) + d := by
  simp [liftCoefficientsRun, tabulateRun_eq]

theorem modelPolynomial (t : ℕ) (ht : 0 < t) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    quotientPolynomial (scalarRing 3 t M cache) (liftCoefficientsRun t a.coefficients).1 =
      a.F t := by
  unfold quotientPolynomial RingModel.Data.F
  congr 1
  funext i
  exact liftCoefficientsRun_correct t ht a.coefficients i

/-- An entirely executable program for the actual supplied ternary polynomial.
Its table and coefficient words can be retained across all later operations. -/
def modelProgram (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    RingProgram (Code (ScalarCode 3 t) d) :=
  quotientProgram (scalarProgram 3 t M cache) (liftCoefficientsRun t a.coefficients).1

/-- Explicit preparation retains both coefficient words and the generated table. -/
def modelProgramRun (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    RingProgram (Code (ScalarCode 3 t) d) × ℕ :=
  let coefficients := liftCoefficientsRun t a.coefficients
  let prepared := quotientProgramRun (scalarProgram 3 t M cache) coefficients.1
  (prepared.1, coefficients.2 + prepared.2)

@[simp] theorem modelProgramRun_value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    (modelProgramRun t a M cache).1 = modelProgram t a M cache := rfl

theorem modelProgramRun_cost (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : ScalarCache 3 t) :
    (modelProgramRun t a M cache).2 ≤
      d * (3 * baseWidth 3 t + 1) + d + setupEventBudget d (scalarMachineBudget 3 t) := by
  have h := quotientProgramRun_cost (scalarProgram 3 t M cache)
    (scalarRing_machineBudget 3 t M cache).program (liftCoefficientsRun t a.coefficients).1
  dsimp only [modelProgramRun]
  rw [liftCoefficientsRun_cost]
  exact Nat.add_le_add_left h _

noncomputable def modelRing (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) : RepresentedRing (Code (ScalarCode 3 t) d) (a.O t) := by
  letI : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  let ops := scalarRing 3 t M cache
  let c := (liftCoefficientsRun t a.coefficients).1
  have hf : quotientPolynomial ops c = a.F t := modelPolynomial t ht a M cache
  exact represented ops (SubexponentialSAT.LiftRing.of (a.F t)) (RingBasis.basis (a.F t))
    (structureTableRun ops.program c).1 (zeroVector ops.program d) (oneVectorRun ops.program d).1
    (by
      intro i j
      rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
      apply Finset.sum_congr rfl
      intro k _
      have hc : ops.decode ((structureTableRun ops.program c).1 i j k) =
          RingBasis.structureConstant (a.F t) i j k := by
        rw [structureTableRun_remainder ops hd]
        change (Polynomial.X^(i.val+j.val) %ₘ quotientPolynomial ops c).coeff k = _
        rw [hf]
        rfl
      rw [hc])
    (by simp only [denote, zeroVector, ops.zero_correct,
      map_zero, zero_mul, Finset.sum_const_zero])
    (by
      have hc (i : Fin d) : ops.decode ((oneVectorRun ops.program d).1 i) =
          RingBasis.coordinates (a.F t) (a.F_monic t ht) (a.F_degree t ht) 1 i := by
        rw [RingBasis.one_coordinates _ _ _ hd]
        exact congrFun (oneVectorRun_correct ops d) i
      unfold denote
      simp_rw [hc]
      exact RingBasis.reconstruct _ _ _ 1)

@[simp] theorem modelRing_program (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) :
    (modelRing t ht hd a M cache).program = modelProgram t a M cache := rfl

/-- The decoder is exactly reconstruction from the model's coefficient basis. -/
theorem modelRing_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    (modelRing t ht hd a M cache).decode x =
      (a.coordinates t ht).symm (fun i => wordValue 3 t (x i)) := by
  change (∑ i, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (x i)) * RingBasis.basis (a.F t) i) = _
  exact (RingBasis.coordinates_symm (a.F t) (a.F_monic t ht) (a.F_degree t ht) _).symm

@[simp] theorem modelRing_coordinates (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    a.coordinates t ht ((modelRing t ht hd a M cache).decode x) =
      (fun i => wordValue 3 t (x i)) := by
  rw [modelRing_decode]
  exact (a.coordinates t ht).apply_symm_apply _

theorem modelRing_decode_lift (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (u : Fin d → ZMod 3) :
    (modelRing t ht hd a M cache).decode (liftCoefficientsRun t u).1 =
      (a.coordinates t ht).symm (fun i => ((u i).val : ZMod (3^t))) := by
  rw [modelRing_decode]
  congr 1
  funext i
  exact liftCoefficientsRun_correct t ht u i

theorem modelRing_readBase (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    a.readBase t ht ((modelRing t ht hd a M cache).decode x) =
      wordValue 3 t (x ⟨0, hd⟩) := by
  have h := congrFun (modelRing_coordinates t ht hd a M cache x) ⟨0, hd⟩
  simpa only [RingModel.Data.coordinates_apply, RingModel.Data.readBase] using h

/-- A canonical coefficient-zero word reads as its exact natural value. -/
theorem modelRing_decodeCount (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d)
    (hx : BinaryArithmetic.toNat (x ⟨0, hd⟩).val < 3^t) :
    a.decodeCount t ht ((modelRing t ht hd a M cache).decode x) =
      BinaryArithmetic.toNat (x ⟨0, hd⟩).val := by
  unfold RingModel.Data.decodeCount
  rw [modelRing_readBase, wordValue, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

theorem modelRing_budget (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) :
    ScalarBudget (modelRing t ht hd a M cache) (eventBudget d (scalarMachineBudget 3 t)) := by
  have h := program_budget (scalarProgram 3 t M cache)
    (scalarRing_machineBudget 3 t M cache).program
    (structureTableRun (scalarProgram 3 t M cache) (liftCoefficientsRun t a.coefficients).1).1
    (zeroVector (scalarProgram 3 t M cache) d) (oneVectorRun (scalarProgram 3 t M cache) d).1
  exact ⟨h.zero, h.one, h.add, h.mul, h.neg⟩

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
