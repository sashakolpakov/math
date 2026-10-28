import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.NumberTheory.ArithmeticGroups.Trace
import OAI.NumberTheory.ArithmeticGroups.Algebraic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! # Degree Two Fixed Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Supporting reduction for the degree-two exclusion. A CM field of
rational degree two has rational fixed scalars, so the negative diagonal
coefficient of the original datum is a negative rational. The isotropy
argument needed to exclude this case is not asserted here. -/

open _root_.NumberField ComplexEmbedding

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem DegreeTwoFixedScalars.cmRealSubfield_finrank_one_of_degree_two
    (hdegree : Module.finrank ℚ E = 2) :
    Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hdegree] at h
  omega

theorem DegreeTwoFixedScalars.cmFixedScalar_isRational_of_degree_two
    (hdegree : Module.finrank ℚ E = 2) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) :
    ∃ q : ℚ, algebraMap ℚ E q = b := by
  let a : maximalRealSubfield E :=
    ⟨b, (NumberField.IsCMField.complexConj_eq_self_iff E b).mp hb⟩
  obtain ⟨q, hq⟩ := _root_.exists_smul_eq_of_finrank_eq_one
    (DegreeTwoFixedScalars.cmRealSubfield_finrank_one_of_degree_two hdegree)
    (one_ne_zero : (1 : maximalRealSubfield E) ≠ 0) a
  rw [Algebra.smul_def, mul_one] at hq
  refine ⟨q, ?_⟩
  calc
    algebraMap ℚ E q =
        algebraMap (maximalRealSubfield E) E
          (algebraMap ℚ (maximalRealSubfield E) q) :=
      IsScalarTower.algebraMap_apply ℚ (maximalRealSubfield E) E q
    _ = b := congrArg (algebraMap (maximalRealSubfield E) E) hq

theorem DegreeTwoFixedScalars.cmNegativeFixedScalar_isNegativeRational_of_degree_two
    (hdegree : Module.finrank ℚ E = 2) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b)
    (φ : E →+* ℂ) (hnegative : (φ b).re < 0) :
    ∃ q : ℚ, q < 0 ∧ algebraMap ℚ E q = b := by
  obtain ⟨q, hq⟩ := DegreeTwoFixedScalars.cmFixedScalar_isRational_of_degree_two hdegree b hb
  have hqre : (q : ℝ) = (φ b).re := by
    rw [← hq]
    simp
  have hqnegative : (q : ℝ) < 0 := hqre.trans_lt hnegative
  refine ⟨q, ?_, hq⟩
  exact_mod_cast hqnegative

theorem Datum.RankThreePELDatum.rational_negative_b_of_degree_two
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hdegree : Module.finrank ℚ E = 2) :
    ∃ q : ℚ, q < 0 ∧ algebraMap ℚ E q = P.b :=
  DegreeTwoFixedScalars.cmNegativeFixedScalar_isNegativeRational_of_degree_two hdegree P.b hP.2.1
    P.μ hP.2.2.2.1

/-- On the fixed field in rational degree two, rational trace has no
nonzero kernel. This is a scalar statement, not an isotropy theorem. -/
theorem DegreeTwoFixedScalars.cmFixedScalar_trace_zero_iff_of_degree_two
    (hdegree : Module.finrank ℚ E = 2) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) :
    Algebra.trace ℚ E b = 0 ↔ b = 0 := by
  obtain ⟨q, rfl⟩ := DegreeTwoFixedScalars.cmFixedScalar_isRational_of_degree_two hdegree b hb
  constructor
  · intro ht
    have hmul : (2 : ℚ) * q = 0 := by
      have htrace := Algebra.trace_algebraMap (R := ℚ) (S := E) q
      have hn : Module.finrank ℚ E • q = 0 := htrace.symm.trans ht
      simpa only [hdegree, nsmul_eq_mul, Nat.cast_ofNat] using hn
    have hq : q = 0 := (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    rw [hq, map_zero]
  · intro hz
    rw [hz, map_zero]

theorem DegreeTwoFixedScalars.cmDegreeTwo_hermitian_trace_zero_iff
    (hdegree : Module.finrank ℚ E = 2) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Algebra.trace ℚ E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b v v) = 0 ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b v v = 0 :=
  DegreeTwoFixedScalars.cmFixedScalar_trace_zero_iff_of_degree_two hdegree (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b v v)
    (NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.hermitian_conjugate b hb v v)

/-- The admissibility hypothesis gives anisotropy of the actual rational
trace form in degree two. Proving that an indefinite rational form of
this dimension is isotropic remains a separate mathematical obligation. -/
theorem Datum.RankThreePELDatum.trace_hermitian_zero_iff_of_degree_two
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hdegree : Module.finrank ℚ E = 2) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Algebra.trace ℚ E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b v v) = 0 ↔ v = 0 := by
  constructor
  · intro ht
    exact hP.2.2.2.2.2.1 v
      ((DegreeTwoFixedScalars.cmDegreeTwo_hermitian_trace_zero_iff hdegree P.b hP.2.1 v).mp ht)
  · intro hv
    subst v
    simp [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian]

/-- The actual rational trace of the original diagonal Hermitian form,
using the existing native bilinear trace construction. -/
def DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm (b : E) : QuadraticForm ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :=
  (NumberTheory.ArithmeticGroups.Algebraic.CongruenceLevel.traceBilinear b 1).toQuadraticMap

@[simp] theorem DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_apply (b : E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm b v = Algebra.trace ℚ E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b v v) := by
  rw [DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
    NumberTheory.ArithmeticGroups.Algebraic.CongruenceLevel.traceBilinear_apply, NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.rationalTrace, one_mul]

theorem DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_axis (b : E) (i : Fin 3) :
    DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm b (Pi.single i 1) =
      Algebra.trace ℚ E (if i = 2 then b else 1) := by
  rw [DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_apply, NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.hermitian_axis,
    Pi.single_eq_same, mul_one]

omit [NumberField.IsCMField E] in
theorem DegreeTwoFixedScalars.cmDegreeTwo_vector_finrank (hdegree : Module.finrank ℚ E = 2) :
    Module.finrank ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 6 := by
  change Module.finrank ℚ (Fin 3 → E) = 6
  rw [Module.finrank_pi_fintype]
  norm_num [hdegree]

theorem Datum.RankThreePELDatum.traceQuadraticForm_anisotropic_of_degree_two
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hdegree : Module.finrank ℚ E = 2) :
    (DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b).Anisotropic := by
  intro v hv
  apply (P.trace_hermitian_zero_iff_of_degree_two hP hdegree v).mp
  simpa only [DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_apply] using hv

theorem Datum.RankThreePELDatum.traceQuadraticForm_has_both_signs_of_degree_two
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hdegree : Module.finrank ℚ E = 2) :
    ∃ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
      0 < DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b u ∧
      DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b v < 0 := by
  obtain ⟨q, hqnegative, hq⟩ := P.rational_negative_b_of_degree_two hP hdegree
  have htrace : Algebra.trace ℚ E (1 : E) = 2 := by
    simpa [hdegree] using (Algebra.trace_algebraMap (R := ℚ) (S := E) (1 : ℚ))
  have hzero : DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b (Pi.single (0 : Fin 3) 1) = 2 := by
    rw [DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_axis]
    simpa using htrace
  have htwo : DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b (Pi.single (2 : Fin 3) 1) =
      (2 : ℚ) * q := by
    rw [DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm_axis, ite_eq_left rfl, ← hq,
      Algebra.trace_algebraMap, hdegree]
    simp [nsmul_eq_mul]
  refine ⟨Pi.single (0 : Fin 3) 1, Pi.single (2 : Fin 3) 1, ?_, ?_⟩
  · rw [hzero]
    norm_num
  · rw [htwo]
    exact mul_neg_of_pos_of_neg (by norm_num) hqnegative

/-- The explicit obstruction to degree-two admissibility. Closing the
exclusion requires proving the general rational isotropy theorem; that
theorem is neither assumed nor introduced as an axiom here. -/
theorem Datum.RankThreePELDatum.degreeTwo_rationalQuadratic_obstruction
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hdegree : Module.finrank ℚ E = 2) :
    ∃ Q : QuadraticForm ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E), Q.Anisotropic ∧
      Module.finrank ℚ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 6 ∧
      ∃ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, 0 < Q u ∧ Q v < 0 :=
  ⟨DegreeTwoFixedScalars.cmHermitianTraceQuadraticForm P.b,
    P.traceQuadraticForm_anisotropic_of_degree_two hP hdegree,
    DegreeTwoFixedScalars.cmDegreeTwo_vector_finrank hdegree,
    P.traceQuadraticForm_has_both_signs_of_degree_two hP hdegree⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
