import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostComponents

namespace OAI.Algorithms

/-! The actual query's CRT tail and returned count width are bounded by the
ordinary cap. All ring bytes and numerical values are produced, not supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ}

 theorem ordinary_base_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ) :
    Width.incomingWidth p+(resources q k occurrence qi hg p.firstWord p.remainingWords).bits+2 ≤ ordinaryCap p occurrence qi := by
  unfold ordinaryCap
  have hp := Nat.le_self_pow (by decide : 4≠0) (Width.incomingWidth p+
    (resources q k occurrence qi hg p.firstWord p.remainingWords).bits+2)
  omega

 theorem ring_word_lengths (p : Preparation q k a hg W V L)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    p.modulus.bits.length ≤ Width.incomingWidth p ∧
      (p.ringState.stacks 202).length ≤ Width.incomingWidth p := by
  have hm : p.out.stacks 194=p.modulus.bits :=
    (p.arithmeticOutput.low 194 (by decide)).trans p.arithmeticOutput.produced.caches.modulus
  have he : p.out.stacks 202=p.ringState.stacks 202 := p.arithmeticOutput.low 202 (by decide)
  have h194 := p.output_width hw 194
  have h202 := p.output_width hw 202
  rw [hm] at h194
  rw [he] at h202
  unfold Width.incomingWidth
  constructor <;> omega

 theorem produced_recovery_scalars (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hn : 2 ≤ ambient q) (hs : SmallInputs q k (ambient q)) :
    let m := Execute.guardedModel (q.input k) p.lengths
    let B := (resources q k occurrence qi hg p.firstWord p.remainingWords).bits
    (packingProblem q k hg).Q ≤ B ∧ (produce (q.input k)).J ≤ B ∧
      m.val 33 ≤ B ∧ m.val 34 ≤ B ∧ 3^(m.val 34) ≤ B+2 ∧
      SubexpLiftRing.baseWidth 3 (m.val 33) ≤ B := by
  dsimp only
  have values (i : Fin 64) := values_le_resources q k occurrence qi (ambient q) hn rfl hs
    hg p.firstWord p.remainingWords p.lengths i
  have hQ := values 21
  have hJ := values 42
  have ht := values 33
  have hd := values 34
  have hfield := values 44
  have hB := values 45
  rw [Serialization.frame _ 21 (by decide) (by decide)] at hQ
  rw [Serialization.frame _ 42 (by decide) (by decide)] at hJ
  rw [Serialization.frame _ 33 (by decide) (by decide)] at ht
  rw [Serialization.frame _ 34 (by decide) (by decide)] at hd
  rw [ring_exponent (q.input k) p.lengths hg] at hfield
  rw [(Serialization.values _).2] at hB
  have hQ' : (packingProblem q k hg).Q ≤ (resources q k occurrence qi hg p.firstWord p.remainingWords).bits := by
    change (produce (q.input k)).Q ≤ _
    rw [←PreparedSource.numeric_Q q k p.lengths]
    exact hQ
  have hJ' : (produce (q.input k)).J ≤ (resources q k occurrence qi hg p.firstWord p.remainingWords).bits := by
    rw [←PreparedSource.numeric_J q k p.lengths hg]
    exact hJ
  refine ⟨hQ',hJ',ht,hd,by omega,?_⟩
  simpa only [RingProgram.ternary_baseWidth] using hB

 theorem prepared_recovery_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) (hn : 2 ≤ ambient q)
    (hs : SmallInputs q k (ambient q)) :
    Count.recoveryBudget (packingProblem q k hg).Q (produce (q.input k)).J
      ((PreparedSource.numeric q k p.lengths).val 33)
      ((PreparedSource.numeric q k p.lengths).val 34)
      p.modulus.bits (p.ringState.stacks 202) ≤ recoveryCoefficient*(ordinaryCap p occurrence qi+1)^96 := by
  obtain ⟨hQ,hJ,ht,hd,hfield,hB⟩ := produced_recovery_scalars p occurrence qi hn hs
  obtain ⟨hm,he⟩ := ring_word_lengths p hw
  have hbase := ordinary_base_le p occurrence qi
  apply recoveryBudget_le
  · exact le_trans hQ (by omega)
  · exact le_trans hJ (by omega)
  · exact le_trans ht (by omega)
  · exact le_trans hd (by omega)
  · exact le_trans hfield (by omega)
  · exact le_trans hm (by omega)
  · exact le_trans he (by omega)

 theorem prepared_countWidth_le (p : Preparation q k a hg W V L) (occurrence qi : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) (hn : 2 ≤ ambient q)
    (hs : SmallInputs q k (ambient q)) :
    p.modulus.bits.length+SubexpLiftRing.baseWidth 3 ((PreparedSource.numeric q k p.lengths).val 33) ≤
      ordinaryCap p occurrence qi := by
  obtain ⟨hQ,hJ,ht,hd,hfield,hB⟩ := produced_recovery_scalars p occurrence qi hn hs
  obtain ⟨hm,he⟩ := ring_word_lengths p hw
  have hbase := ordinary_base_le p occurrence qi
  change p.modulus.bits.length+SubexpLiftRing.baseWidth 3 ((Execute.guardedModel (q.input k) p.lengths).val 33) ≤ _
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
