import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramMetadata
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic ModularArithmetic

/-- Normalize a temporary word in stack zero, using the cached unary width. -/
abbrev normalize (target : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt 12 7 38)
    (.seq (callLow normalizeProgram) (IdempotentProgram.storeResult target))

theorem normalize_eval (d : Data) (m input shape : List Bool) (target : Fin 41)
    (ht : 8 ≤ target.val) (ht38 : target ≠ 38)
    (h12 : d.stacks 12=shape) (h0 : d.stacks 0=input)
    (hrest : ∀ i : Fin 8, i ≠ 0 → d.stacks (low i)=if i=5 then m else [])
    (h38 : d.stacks 38=[]) :
    ∃ n e, Eval (normalize target) n d e ∧
      e.stacks=Function.update (Function.update d.stacks target (padTo shape input)) 0 [] ∧
      n ≤ 23*shape.length+2*input.length+2*(d.stacks target).length+25 := by
  let a := ArithmeticCalls.afterCopy 12 7 d
  have h7 : d.stacks 7=[] := by simpa [low] using hrest 7 (by decide)
  have cp := ArithmeticCalls.copyAt_eval (12:Fin 41) 7 38 d (by decide) (by decide)
    (by decide) h7 h38
  obtain ⟨rf,n,hn,run⟩ := normalize_correct a.regs input shape m
  have ht0 : target ≠ 0 := by intro h; subst target; contradiction
  have ht7 : target ≠ 7 := by intro h; subst target; omega
  obtain ⟨e,he,hes⟩ := callLow_eval normalizeProgram a
    ⟨a.regs,normalizationState input shape [] m⟩
    ⟨rf,normalizationState (padTo shape input) [] [] m⟩
    (Function.update d.stacks 0 (padTo shape input)) n rfl (by
      intro i
      by_cases hi : i=0
      · subst i; simp [a,ArithmeticCalls.afterCopy,low,normalizationState,h0]
      · have hh := hrest i hi
        fin_cases i <;> simp_all [a,ArithmeticCalls.afterCopy,low,normalizationState])
    (by
      intro i
      by_cases hi : i=0
      · subst i; rfl
      · have hh := hrest i hi
        fin_cases i <;> simp_all [low,normalizationState])
    (by
      intro j hj
      have hj0 : j≠0 := by intro h; subst j; omega
      have hj7 : j≠7 := by intro h; subst j; omega
      simp [a,ArithmeticCalls.afterCopy,hj0,hj7]) run
  have st := IdempotentProgram.storeResult_eval e target ht0 ht38 (by rw [hes]; simpa using h38)
  refine ⟨_,IdempotentProgram.storedResult e target,cp.seq (he.seq st),?_,?_⟩
  · rw [IdempotentProgram.storedResult_stacks e target ht0,hes]
    funext j
    by_cases hj : j=0
    · subst j; simp
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · simp only [hes,Function.update_same,padTo_length]
    have hlen : (a.stacks 12).length=shape.length := by simp [a,ArithmeticCalls.afterCopy,h12]
    simp only [h12,Function.update_of_ne ht0] at *
    omega

abbrev literal (target : Fin 41) (bits : List Bool) : Cmd 8 41 :=
  .seq (literalAt 0 bits) (normalize target)

theorem literal_eval (d : Data) (m shape : List Bool) (target : Fin 41)
    (bits : List Bool) (h : Rest d m) (h12 : d.stacks 12=shape)
    (ht : 8 ≤ target.val) (ht38 : target≠38) :
    ∃ n e, Eval (literal target bits) n d e ∧
      e.stacks=Function.update d.stacks target (padTo shape bits) ∧
      n ≤ 23*shape.length+4*bits.length+2*(d.stacks target).length+25 := by
  let a := literalResult d 0 bits
  have h0 : d.stacks 0=[] := by simpa [low] using h.1 0
  have ha : a.stacks=Function.update d.stacks 0 bits := by simp [a,literalResult_stacks,h0]
  obtain ⟨n,e,he,hes,hn⟩ := normalize_eval a m bits shape target ht ht38
    (by simp [ha,h12]) (by simp [ha]) (by
      intro i hi
      have hlow : low i ≠ 0 := by intro h; apply hi; exact low_injective h
      simpa [ha,hlow] using h.1 i) (by simp [ha,h.2])
  have ht0 : target≠0 := by intro h; subst target; omega
  refine ⟨_,e,(literalAt_eval d 0 bits).seq he,?_,?_⟩
  · rw [hes,ha]
    funext j
    by_cases hj : j=0
    · subst j; simp [ht0.symm,h0]
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · simp only [ha,Function.update_of_ne ht0] at hn
    omega

def decrementPorts : CounterForPrograms.Ports 8 41 where
  register := ⟨Fin.castAdd 5, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  counter := 0
  scratch := 2
  counter_ne_scratch := by decide

abbrev negativeOne (target : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt 5 0 38)
    (.seq (CounterForPrograms.decrementCmd decrementPorts) (normalize target))

theorem negativeOne_eval (d : Data) (m shape : List Bool) (target : Fin 41)
    (h : Rest d m) (h12 : d.stacks 12=shape) (hm : 0 < BinaryArithmetic.toNat m)
    (ht : 8 ≤ target.val) (ht38 : target≠38) :
    ∃ n e, Eval (negativeOne target) n d e ∧
      e.stacks=Function.update d.stacks target (padTo shape (CounterPrograms.ripple false m)) ∧
      n ≤ 23*shape.length+17*m.length+2*(d.stacks target).length+38 := by
  let a := ArithmeticCalls.afterCopy 5 0 d
  let b := CounterForPrograms.decrementResult decrementPorts a
  have h0 : d.stacks 0=[] := by simpa [low] using h.1 0
  have h5 : d.stacks 5=m := by simpa [low] using h.1 5
  have ha : a.stacks=Function.update d.stacks 0 m := by simp [a,ArithmeticCalls.afterCopy,h5]
  have cp := ArithmeticCalls.copyAt_eval (5:Fin 41) 0 38 d (by decide) (by decide)
    (by decide) h0 h.2
  have h2 : a.stacks 2=[] := by simpa [ha,low] using h.1 2
  have dc := CounterForPrograms.decrement_eval decrementPorts a h2
  have hb : b.stacks=Function.update d.stacks 0 (CounterPrograms.ripple false m) := by
    funext j
    by_cases hj0 : j=0
    · subst j
      change (CounterForPrograms.decrementResult decrementPorts a).stacks decrementPorts.counter = _
      rw [CounterForPrograms.decrementResult_counter]
      simp [decrementPorts,ha]
    · by_cases hj2 : j=2
      · subst j
        change (CounterForPrograms.decrementResult decrementPorts a).stacks decrementPorts.scratch = _
        rw [CounterForPrograms.decrementResult_scratch]
        simpa [low] using (h.1 2).symm
      · rw [show b.stacks j = a.stacks j from
          CounterForPrograms.install_other_stack decrementPorts a _ _ _ _ _ j hj0 hj2]
        simp [ha,hj0]
  obtain ⟨n,e,he,hes,hn⟩ := normalize_eval b m (CounterPrograms.ripple false m) shape target
    ht ht38 (by simp [hb,h12]) (by simp [hb]) (by
      intro i hi
      have hlow : low i≠0 := by intro h; apply hi; exact low_injective h
      simpa [hb,hlow] using h.1 i) (by simp [hb,h.2])
  have ht0 : target≠0 := by intro h; subst target; omega
  refine ⟨_,e,cp.seq (dc.seq he),?_,?_⟩
  · rw [hes,hb]
    funext j
    by_cases hj : j=0
    · subst j; simp [ht0.symm,h0]
    · by_cases hjt : j=target
      · subst j; simp [ht0]
      · simp [hj,hjt]
  · have hc := CounterPrograms.rippleCost_le false m
    have hmv : 0 < CounterPrograms.value m := by simpa [CounterPrograms.value_eq_toNat] using hm
    have hl := CounterPrograms.decrement_length hmv
    simp only [hb,Function.update_of_ne ht0] at hn
    simp only [decrementPorts,ha,Function.update_same,h5]
    rw [hl] at hn
    omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
