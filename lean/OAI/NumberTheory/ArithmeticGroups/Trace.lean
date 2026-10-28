import OAI.NumberTheory.ArithmeticGroups.Data
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

/-! # Trace -/

namespace OAI.NumberTheory.ArithmeticGroups.Trace.CongruenceLevel

noncomputable section

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

def rationalTrace (b δ : E) (x y : Data.CongruenceLevel.VE E) : ℚ :=
  Algebra.trace ℚ E (δ * Data.CongruenceLevel.hermitian b x y)

omit [Algebra ℚ E] in
lemma hermitian_smul_left (b a : E) (x y : Data.CongruenceLevel.VE E) :
    Data.CongruenceLevel.hermitian b (a • x) y = a * Data.CongruenceLevel.hermitian b x y := by
  simp only [Data.CongruenceLevel.hermitian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Algebra ℚ E] in
lemma hermitian_smul_right (b a : E) (x y : Data.CongruenceLevel.VE E) :
    Data.CongruenceLevel.hermitian b x (a • y) =
      NumberField.IsCMField.complexConj E a * Data.CongruenceLevel.hermitian b x y := by
  simp only [Data.CongruenceLevel.hermitian, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [NumberField.IsCMField E] in
lemma trace_separates (δ : E) (hδ : δ ≠ 0) (u v : E)
    (h : ∀ a : E, Algebra.trace ℚ E (δ * (a * u)) =
      Algebra.trace ℚ E (δ * (a * v))) : u = v := by
  have hz : δ * (u - v) = 0 := by
    apply (traceForm_nondegenerate ℚ E).1
    intro a
    change Algebra.trace ℚ E (δ * (u - v) * a) = 0
    have he : δ * (u - v) * a = δ * (a * u) - δ * (a * v) := by ring
    rw [he, map_sub, h a, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hδ)

/-- Restricting to E-linear automorphisms recovers the original unitary group. -/
theorem trace_isometries_iff (b δ : E) (hδ : δ ≠ 0)
    (g : Data.CongruenceLevel.VE E ≃ₗ[E] Data.CongruenceLevel.VE E) :
    (∀ x y, rationalTrace b δ (g x) (g y) = rationalTrace b δ x y) ↔
    (∀ x y, Data.CongruenceLevel.hermitian b (g x) (g y) = Data.CongruenceLevel.hermitian b x y) := by
  constructor
  · intro hg x y
    apply trace_separates δ hδ
    intro a
    have h := hg (a • x) y
    simpa only [rationalTrace, map_smul, hermitian_smul_left] using h
  · intro hg x y
    simp only [rationalTrace, hg]

lemma trace_rosati (b δ a : E) (x y : Data.CongruenceLevel.VE E) :
    rationalTrace b δ (a • x) y =
      rationalTrace b δ x (NumberField.IsCMField.complexConj E a • y) := by
  simp only [rationalTrace, hermitian_smul_left, hermitian_smul_right,
    NumberField.IsCMField.complexConj_apply_apply]

omit [Algebra ℚ E] in
lemma hermitian_conjugate (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) (x y : Data.CongruenceLevel.VE E) :
    NumberField.IsCMField.complexConj E (Data.CongruenceLevel.hermitian b x y) = Data.CongruenceLevel.hermitian b y x := by
  simp only [Data.CongruenceLevel.hermitian, map_sum, map_mul,
    NumberField.IsCMField.complexConj_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [hb, map_one] <;> ring

lemma rationalTrace_skew (b δ : E)
    (hb : NumberField.IsCMField.complexConj E b = b)
    (hδ : NumberField.IsCMField.complexConj E δ = -δ) (x y : Data.CongruenceLevel.VE E) :
    rationalTrace b δ x y = -rationalTrace b δ y x := by
  calc
    rationalTrace b δ x y = Algebra.trace ℚ E
        (AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (δ * Data.CongruenceLevel.hermitian b x y)) :=
      (Algebra.trace_eq_of_algEquiv (AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E) _).symm
    _ = -rationalTrace b δ y x := by
      change Algebra.trace ℚ E
        (NumberField.IsCMField.complexConj E (δ * Data.CongruenceLevel.hermitian b x y)) = _
      rw [map_mul, hδ, hermitian_conjugate b hb, neg_mul, map_neg]
      rfl

lemma rationalTrace_alternating (b δ : E)
    (hb : NumberField.IsCMField.complexConj E b = b)
    (hδ : NumberField.IsCMField.complexConj E δ = -δ) (x : Data.CongruenceLevel.VE E) :
    rationalTrace b δ x x = 0 := by
  have h := rationalTrace_skew b δ hb hδ x x
  linarith

omit [Algebra ℚ E] in
lemma hermitian_axis (b : E) (x : Data.CongruenceLevel.VE E) (i : Fin 3) :
    Data.CongruenceLevel.hermitian b x (Pi.single i 1) = (if i = 2 then b else 1) * x i := by
  classical
  by_cases hi : i = 2 <;> simp [Data.CongruenceLevel.hermitian, Pi.single_apply, apply_ite, hi]

omit [Algebra ℚ E] in
lemma hermitian_nondegenerate (b : E) (hb : b ≠ 0) (x : Data.CongruenceLevel.VE E)
    (hx : ∀ y, Data.CongruenceLevel.hermitian b x y = 0) : x = 0 := by
  ext i
  have h := hx (Pi.single i 1)
  rw [hermitian_axis] at h
  have hc : (if i = 2 then b else 1) ≠ 0 := by split_ifs <;> simp_all
  exact (mul_eq_zero.mp h).resolve_left hc

lemma rationalTrace_nondegenerate (b δ : E) (hb : b ≠ 0) (hδ : δ ≠ 0)
    (x : Data.CongruenceLevel.VE E) (hx : ∀ y, rationalTrace b δ x y = 0) : x = 0 := by
  apply hermitian_nondegenerate b hb x
  intro y
  apply trace_separates δ hδ _ 0
  intro a
  have h := hx (NumberField.IsCMField.complexConj E a • y)
  simpa only [rationalTrace, hermitian_smul_right,
    NumberField.IsCMField.complexConj_apply_apply, mul_zero, map_zero] using h

end

end OAI.NumberTheory.ArithmeticGroups.Trace.CongruenceLevel
