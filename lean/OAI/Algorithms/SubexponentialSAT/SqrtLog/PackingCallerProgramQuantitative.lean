import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramEnvelope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsPolynomial

namespace OAI.Algorithms

/-! Polynomial time and output space for the complete native packing
caller, including global staging, cleanup, and master-bank parking. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage

def globalSize (a : Wide.Data) (p : Problem) :=
  inputMass a+Bounds.scalarSize (Wide.parameterStore (Wide.project a)) p+1

theorem budget_polynomial : ∃ C d : ℕ, 1 ≤ d ∧
    ∀ (a : Wide.Data) (p : Problem) (w : Word p.r p.Q) (tail : List (Word p.r p.Q)),
    Sources a p → Empty a →
    (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q →
    budget a p w tail ≤ C*(globalSize a p)^d ∧
    WordBound (C*(globalSize a p)^d) (result a p w tail) := by
  obtain ⟨cc,dc,hc⟩ := Bounds.coreBudget_polynomial
  obtain ⟨cb,db,hb⟩ := Bounds.bankOutput_word_polynomial
  refine ⟨combinedConstant cc cb,combinedExponent dc db,le_max_left _ _,?_⟩
  intro a p w tail hs he hrows
  have hsize : Bounds.scalarSize (Wide.parameterStore (Wide.project a)) p+1 ≤ globalSize a p := by
    unfold globalSize; omega
  apply polynomial_envelope a p he w tail (globalSize a p) cc dc cb db
    (by unfold globalSize; omega) (by unfold globalSize; omega)
  · exact (hc _ p w tail hs.parameters hrows).trans
      (Nat.mul_le_mul_left cc (Nat.pow_le_pow_left hsize dc))
  · intro i
    exact (hb a p w tail i).trans (Nat.mul_le_mul_left cb (Nat.pow_le_pow_left hsize db))

theorem quantitative_run : ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
    ∀ (a : Wide.Data) (p : Problem), Sources a p → Empty a →
    ∃ w : Word p.r p.Q, ∃ tail : List (Word p.r p.Q), ∃ b : Wide.Data,
      (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q ∧
      (w::tail).Nodup ∧ (∀ z,z∈w::tail) ∧
      Computation.RunsIn (primitive program).step (C*(globalSize a p)^d)
        (primitiveCfg program (a.withPC (some program.entry)))
        (primitiveCfg program (b.withPC none)) ∧
      b.stacks=(result a p w tail).stacks ∧
      (∀ i,(b.stacks i).length ≤ C*(globalSize a p)^d) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) := by
  obtain ⟨C,d,hd,hpoly⟩ := budget_polynomial
  let K := (primitiveOverhead program+1)*C+1
  have hK : 1 ≤ K := by unfold K; omega
  have hCK : C ≤ K := by unfold K; nlinarith
  have hPK : primitiveOverhead program*C ≤ K := by unfold K; nlinarith
  refine ⟨K,d,hK,hd,?_⟩
  intro a p hs he
  obtain ⟨w,tail,b,hrows,hn,hall,hRun,hbs,hbr⟩ := ordered_run a p hs he
  obtain ⟨hcost,hsize⟩ := hpoly a p w tail hs he hrows
  have htime : primitiveOverhead program*budget a p w tail ≤ K*(globalSize a p)^d := by
    calc
      _ ≤ primitiveOverhead program*(C*(globalSize a p)^d) := Nat.mul_le_mul_left _ hcost
      _ = (primitiveOverhead program*C)*(globalSize a p)^d := by rw [Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_right _ hPK
  refine ⟨w,tail,b,hrows,hn,hall,(primitive_execution program hRun).mono htime,hbs,?_,hbr⟩
  intro i
  rw [hbs]
  exact (hsize i).trans (Nat.mul_le_mul_right _ hCK)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
