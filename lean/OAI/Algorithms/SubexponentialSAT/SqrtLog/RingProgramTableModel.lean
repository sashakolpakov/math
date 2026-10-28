import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableMachine
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def modelCoefficients (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    List.Vector (Word (baseWidth 3 t)) d :=
  List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1

@[simp] theorem modelCoefficients_get (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    (modelCoefficients t a).get = (RingProgram.liftCoefficientsRun t a.coefficients).1 := by
  funext i
  exact List.Vector.get_ofFn _ _

def preparedStore (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d) (s : Store) : Store :=
  ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
    c (iterData p t M cache.zero cache.minusOne c (2*d-2)
      (initialData d cache.one cache.zero)) cache.zero cache.minusOne

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) : List Bool :=
  RingTriple.tableEncoding (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

/-- Native preparation from supplied coefficient words. The modulus,
polynomial, degree, width, zero, and minus-one caches remain available.
The one-word seed on port 0 is consumed. -/
theorem model_program_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth 3 t) (hdegree : s.degree.length = d) :
    let cache := (RingProgram.prepareScalarCache 3 t M ht).1
    let c := modelCoefficients t a
    ∃ rf, RunsIn Machine.program (208000*(d+1)^5*(t+1)^2)
      ((Machine.state regs (initialStore s c cache.one cache.zero cache.minusOne) []).withPC
        (some Machine.program.entry))
      ((Machine.state rf (preparedStore 3 t M cache c s) (modelTable t a M cache)).withPC none) := by
  dsimp only
  let cache := (RingProgram.prepareScalarCache 3 t M ht).1
  let c := modelCoefficients t a
  obtain ⟨rf,n,hn,htrace⟩ := Machine.program_run 3 t M cache hd c
    (RingProgram.prepareScalarCache_zero_canonical 3 t M ht)
    (RingProgram.prepareScalarCache_one_canonical 3 t M ht) s regs hmod hw hdegree
  refine ⟨rf,n,?_,?_⟩
  · apply hn.trans
    apply (Machine.nativeBudget_polynomial (baseWidth 3 t) d).trans
    rw [RingProgram.ternary_baseWidth]
    have h : (2*t+1)^2 ≤ 4*(t+1)^2 := by nlinarith
    nlinarith [Nat.mul_le_mul_left (52000*(d+1)^5) h]
  · simpa only [preparedStore, modelTable, c, modelCoefficients_get] using htrace

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
