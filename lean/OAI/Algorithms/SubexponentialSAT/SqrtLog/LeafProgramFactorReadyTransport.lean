import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyCore

namespace OAI.Algorithms

/-! The physical source contract survives changes only to loop/parser data
and to the current factor counter. The size hypothesis is discharged separately. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing DensePolynomialProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}

theorem source_transfer {a b : State 16 768} {v n f g S : ℕ}
    (h : SourceReady.Input p ps P a v n f S) (ha : Agree b.stacks a.stacks)
    (hf : b.stacks 556=List.replicate g true)
    (hs : ∀ i,(b.stacks i).length ≤ S) : SourceReady.Input p ps P b v n g S := by
  constructor
  · apply h.arithmetic.frame_low
    intro i hi
    apply ha
    intro hm
    simp [changes, SourceReady.localPort, LayoutSourceRowsProgram.executorPorts,
      Fin.ext_iff] at hm
    omega
  · intro i hi
    have hne : SourceReady.localPort i ∉ changes := by
      intro hm
      apply hi
      simp [changes, SourceReady.localPort, Fin.ext_iff] at hm
      have he : i=(216 : Fin 340) := Fin.ext (by omega)
      subst i
      simp [SourceReady.physicalLive]
    exact (ha _ hne).trans (h.clean i hi)
  · exact (ha 684 (by decide)).trans h.tmp
  · intro i hi
    have hne : i ∉ changes := by
      simp only [SourceStaging.backupPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> simp [changes]
    exact (ha i hne).trans (h.backups i hi)
  · exact (ha _ (by decide)).trans h.dimension
  · exact (ha _ (by decide)).trans h.ambient
  · exact hf
  · exact (ha _ (by decide)).trans h.literal
  · exact (ha _ (by decide)).trans h.colors
  · exact (ha _ (by decide)).trans h.nodes
  · exact (ha _ (by decide)).trans h.typeWidth
  · exact (ha _ (by decide)).trans h.positive
  · exact (ha _ (by decide)).trans h.negative
  · exact (ha _ (by decide)).trans h.scalarWidth
  · exact (ha _ (by decide)).trans h.power
  · exact h.powerNegative
  · exact (ha _ (by decide)).trans h.radius
  · exact (ha _ (by decide)).trans h.offset
  · exact (ha _ (by decide)).trans h.metadata
  · exact (ha _ (by decide)).trans h.plans
  · exact (ha _ (by decide)).trans h.inverses
  · exact (ha _ (by decide)).trans h.negatives
  · exact (ha _ (by decide)).trans h.differences
  · exact (ha _ (by decide)).trans h.ringWidth
  · exact (ha _ (by decide)).trans h.rowWidth
  · exact (ha _ (by decide)).trans h.zero
  · exact (ha _ (by decide)).trans h.one
  · exact (ha _ (by decide)).trans h.minusOne
  · exact (ha _ (by decide)).trans h.inverseDenominator
  · exact hs
  · exact h.arraySize
  · exact h.countSize
  · exact h.metadataSize
  · exact h.incidenceBound

theorem caller_transfer {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J R n : ℕ} {theta : Coeff (baseWidth 3 t) d} {a b : State 16 768}
    (h : CallerInput t model M cache J R theta a n) (ha : Agree b.stacks a.stacks) :
    CallerInput t model M cache J R theta b n := by
  constructor
  · exact h.widthPositive
  · exact h.zeroCanonical
  · exact h.zeroBits
  · exact (ha _ (by decide)).trans h.modulus
  · rw [ha _ (by decide)]; exact h.width
  · exact (ha _ (by decide)).trans h.zero
  · exact (ha _ (by decide)).trans h.table
  · rw [ha _ (by decide)]; exact h.degree
  · rw [ha _ (by decide)]; exact h.choicesLength
  · exact (ha _ (by decide)).trans h.zeroWord
  · exact (ha _ (by decide)).trans h.oneWord
  · exact (ha _ (by decide)).trans h.thetaWord
  · exact (ha _ (by decide)).trans h.ambientCount
  · exact (ha _ (by decide)).trans h.targetCount
  · exact (ha _ (by decide)).trans h.radius
  · rw [ha _ (by decide)]; exact h.highLength
  · intro i hlo hhi hne
    have hn : i ∉ changes := by
      simp only [changes,List.mem_cons,List.mem_nil_iff,or_false,not_or]
      refine ⟨?_,?_,?_,?_,hne⟩ <;> intro he <;> subst i <;> norm_num at hlo
    exact (ha i hn).trans (h.workerEmpty i hlo hhi hne)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms
