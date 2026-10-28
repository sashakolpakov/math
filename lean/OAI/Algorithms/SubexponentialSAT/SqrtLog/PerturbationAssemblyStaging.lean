import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidenceFrame

namespace OAI.Algorithms

/-! The common perturbation input invariant follows from the actual paid leaf
staging copies and a clean worker. The full source count is built as R+1. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure CallerInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J R : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterData) (n : ℕ) : Prop where
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  modulus : s.stacks 194=M.bits
  width : (s.stacks 202).length=baseWidth 3 t
  zero : s.stacks 203=cache.zero.val
  table : s.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s.stacks 204).length=d
  choicesLength : (s.stacks 145).length=n
  zeroWord : s.stacks 280=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s.stacks 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s.stacks 78=RingProgram.flat theta
  ambientCount : s.stacks 128=List.replicate n true
  targetCount : s.stacks 243=List.replicate J true
  radius : s.stacks 138=List.replicate R true
  highLength : (s.stacks 703).length=n
  workerEmpty : ∀ i:Fin 768,340 ≤ i.val → i.val < 680 → i≠556 → s.stacks i=[]

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J R : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterData} {n : ℕ}

theorem CallerInput.destinations_empty (h : CallerInput t a M cache J R theta s n) :
    ∀ p∈LeafProgram.Incidence.pairs,s.stacks p.2=[] := by
  intro p hp
  have hb : 340 ≤ p.2.val ∧ p.2.val < 680 ∧ p.2≠556 := by
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> subst p <;> decide
  exact h.workerEmpty p.2 hb.1 hb.2.1 hb.2.2

private theorem innerPort_ne_550_of_small (i : Fin 256) (hi : i.val < 205) :
    innerPort i ≠ 550 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  omega

private theorem innerPort_ne_556_of_small (i : Fin 256) (hi : i.val < 205) :
    innerPort i ≠ 556 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  omega

private theorem innerPort_ne_incidence_of_small (i : Fin 256) (hi : i.val < 205)
    (hn : i ∉ arithmeticCachePorts) (p : Fin 768 × Fin 768)
    (hp : p ∈ LeafProgram.Incidence.pairs) : innerPort i ≠ p.2 := by
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;>
    subst p <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp [innerPort] at hv
    simp [arithmeticCachePorts] at hn
    omega

private theorem innerPort_ne_550_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch) :
    innerPort i ≠ 550 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

private theorem innerPort_ne_556_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch) :
    innerPort i ≠ 556 := by
  intro h
  have hv := congrArg Fin.val h
  simp [innerPort] at hv
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

private theorem innerPort_ne_incidence_of_lowScratch (i : Fin 256) (hi : i ∈ lowScratch)
    (hlarge : 205 ≤ i.val) (p : Fin 768 × Fin 768)
    (hp : p ∈ LeafProgram.Incidence.pairs) : innerPort i ≠ p.2 := by
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;>
    subst p <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp [innerPort] at hv
    omega

theorem CallerInput.staged (h : CallerInput t a M cache J R theta s n) :
    StagedInput t a M cache J (R+1) theta (LeafProgram.Incidence.staged s).stacks n := by
  have hc := LeafProgram.Incidence.staged_copy s h.destinations_empty
  have ht := LeafProgram.Incidence.staged_cutoff s R h.radius (h.workerEmpty 550 (by decide) (by decide) (by decide))
  have hwidth : (LeafProgram.Incidence.staged s).stacks 551=s.stacks 280 := hc (280,551) (by decide)
  refine ⟨?_,h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hc (194,534) (by decide)).trans h.modulus
    · change (LeafProgram.Incidence.staged s).stacks 345=(LeafProgram.Incidence.staged s).stacks 534
      rw [hc (194,345) (by decide),hc (194,534) (by decide)]
    · change ((LeafProgram.Incidence.staged s).stacks 542).length=_
      rw [hc (202,542) (by decide)]; exact h.width
    · change (LeafProgram.Incidence.staged s).stacks 350=(LeafProgram.Incidence.staged s).stacks 542
      rw [hc (202,350) (by decide),hc (202,542) (by decide)]
    · exact (hc (203,543) (by decide)).trans h.zero
    · exact (hc (201,541) (by decide)).trans h.table
    · change ((LeafProgram.Incidence.staged s).stacks 544).length=_
      rw [hc (204,544) (by decide)]; exact h.degree
    · exact ((hc (280,444) (by decide)).trans h.zeroWord).trans h.zeroBits
    · intro i hi hn
      have hp : innerPort i≠550 ∧ ∀ p∈LeafProgram.Incidence.pairs,innerPort i≠p.2 := by
        constructor
        · exact innerPort_ne_550_of_small i hi
        · intro p hmem
          exact innerPort_ne_incidence_of_small i hi hn p hmem
      change (LeafProgram.Incidence.staged s).stacks (innerPort i)=[]
      rw [LeafProgram.Incidence.staged_frame s (innerPort i) hp.1 hp.2]
      apply h.workerEmpty
      · dsimp [innerPort]; omega
      · dsimp [innerPort]; omega
      · exact innerPort_ne_556_of_small i hi
  · rw [hc (145,546) (by decide)]; exact h.choicesLength
  · exact (hc (280,547) (by decide)).trans h.zeroWord
  · exact (hc (207,548) (by decide)).trans h.oneWord
  · exact (hc (78,549) (by decide)).trans h.thetaWord
  · simp [ht]
  · rw [hwidth,h.zeroWord]; exact RingProgram.flat_length _
  · exact (hc (128,552) (by decide)).trans h.ambientCount
  · exact (hc (243,553) (by decide)).trans h.targetCount
  · intro i hi hlarge
    have hp : innerPort i≠550 ∧ ∀ p∈LeafProgram.Incidence.pairs,innerPort i≠p.2 := by
      constructor
      · exact innerPort_ne_550_of_lowScratch i hi
      · intro p hmem
        exact innerPort_ne_incidence_of_lowScratch i hi hlarge p hmem
    rw [LeafProgram.Incidence.staged_frame s (innerPort i) hp.1 hp.2]
    apply h.workerEmpty
    · dsimp [innerPort]; omega
    · dsimp [innerPort]; omega
    · exact innerPort_ne_556_of_lowScratch i hi

theorem CallerInput.staged_high (h : CallerInput t a M cache J R theta s n) :
    ((LeafProgram.Incidence.staged s).stacks 575).length=n := by
  rw [LeafProgram.Incidence.staged_copy s h.destinations_empty (703,575) (by decide)]
  exact h.highLength

theorem CallerInput.staged_empty (h : CallerInput t a M cache J R theta s n)
    (i : Fin 768) (hi : i∈([460,545,555,557,561,569,573,585] : List (Fin 768))) :
    (LeafProgram.Incidence.staged s).stacks i=[] := by
  have hb : 340 ≤ i.val ∧ i.val < 680 ∧ i≠556 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with hi|hi|hi|hi|hi|hi|hi|hi <;> subst i <;> decide
  have hc : i≠550 := by
    intro he; subst i; norm_num [Fin.ext_iff] at hi
  have hp : ∀ p∈LeafProgram.Incidence.pairs,i≠p.2 := by
    intro p hmem
    simp only [LeafProgram.Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hmem
    rcases hmem with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh <;> subst p
    all_goals intro he; subst i; norm_num [Fin.ext_iff] at hi
  rw [LeafProgram.Incidence.staged_frame s i hc hp]
  exact h.workerEmpty i hb.1 hb.2.1 hb.2.2

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
