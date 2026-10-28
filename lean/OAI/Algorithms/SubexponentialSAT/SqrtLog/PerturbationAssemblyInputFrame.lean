import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInput

namespace OAI.Algorithms

/-! Low preparation is independent of the selected literal/factor IDs and
outer table accumulator. This gives the caller a reusable loop invariant. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def inputFrame (s u : Store) : Prop :=
  ∀ i,i≠215 → i≠216 → i≠229 → i≠233 → i≠234 → i≠235 → u i=s i

theorem LowInput.frame {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s u : Store}
    (h : LowInput t a M cache J N theta rows s) (hf : inputFrame s u) :
    LowInput t a M cache J N theta rows u := by
  have low : CRTLocalProgram.LowFrame s u := by
    intro i hi
    apply hf i
    all_goals intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h10 := low 10 (by decide)
  refine ⟨h.widthPositive,h.zeroCanonical,?_,h.scalarReady.frame low,?_,?_,?_,h.zeroBits,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [h10] using PairSpec.BaseReady.frame 3 t M cache _ h.pairReady low
  · intro i
    rw [low _ (by fin_cases i <;> decide)]
    exact h.buffersEmpty i
  · exact (low 121 (by decide)).trans h.empty121
  · exact (low 122 (by decide)).trans h.empty122
  · exact (hf 205 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sourceRows
  · exact (hf 206 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.choices
  · exact (hf 207 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.zeroWord
  · exact (hf 208 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.oneWord
  · exact (hf 209 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.thetaWord
  · simpa only [hf 210 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] using h.sourceCount
  · simpa only [hf 211 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] using h.wordWidth
  · simpa only [hf 212 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] using h.ambientCount
  · exact (hf 213 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.targetCount
  · exact (low 104 (by decide)).trans h.widthZeros
  · intro i hi
    have hn : i ≠ 215 ∧ i ≠ 216 ∧ i ≠ 229 ∧ i ≠ 233 ∧ i ≠ 234 ∧ i ≠ 235 := by
      simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
        coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
      omega
    exact (hf i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).trans (h.workEmpty i hi)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
