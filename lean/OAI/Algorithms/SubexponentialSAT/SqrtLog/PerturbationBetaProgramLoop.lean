import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramStep

namespace OAI.Algorithms

/-! Paid outer traversal. Every row frame and matching assignment bit is
consumed; selected rows call the actual scalar Horner and addition programs. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

def peekReady {t d : ℕ} (regs : Fin 16 → Bool) (base : Store)
    (rows : List (List (Coeff t d) × Bool)) (acc : Coeff t d) : Data :=
  ⟨readRegs regs 0 1 (rowsBits rows).head?,ready base rows acc⟩

theorem peekRow_eval {t d : ℕ} (regs : Fin 16 → Bool) (base : Store)
    (rows : List (List (Coeff t d) × Bool)) (acc : Coeff t d) :
    Eval peekRow 1 (⟨regs,ready base rows acc⟩ : Data) (peekReady regs base rows acc) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem loop_eval (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=L) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[])
    (regs : Fin 16 → Bool) :
    ∃ ns rf, ns ≤ rows.length*(stepBudget L t d+2)+1 ∧
      Eval loop ns (peekReady regs base rows acc)
        (⟨rf,ready base [] (rows.foldl (stepValue t a M cache theta) acc)⟩ : Data) := by
  induction rows generalizing regs acc with
  | nil =>
    refine ⟨1,(peekReady regs base [] acc).regs,by simp,?_⟩
    exact Eval.while_false (by simp [peekReady,rowsBits,Encoding.encodeList,readRegs])
  | cons row rows ih =>
    rcases row with ⟨P,b⟩
    have hl : P.length=L := hL (P,b) (by simp)
    obtain ⟨ns,rs,hns,hes⟩ := step_run t a M cache hz base hready theta acc P b rows
      hx hz0 (hc.trans hl.symm) hw h232 h240 h246 h248 h241 h244 h245 h251 h252
      (peekReady regs base ((P,b)::rows) acc).regs
    obtain ⟨nt,rt,hnt,het⟩ := ih (stepValue t a M cache theta acc (P,b))
      (fun row hr => hL row (by simp [hr])) rs
    have hg : (peekReady regs base ((P,b)::rows) acc).regs 0=true := by
      simp [peekReady,rowsBits,Encoding.encodeList,readRegs]
    have hp := peekRow_eval rs base rows (stepValue t a M cache theta acc (P,b))
    have h := Eval.while_true hg (hes.seq hp) het
    refine ⟨ns+1+nt+1,rt,?_,?_⟩
    · rw [hl] at hns
      simp only [List.length_cons]
      nlinarith
    · simpa only [loop, body, List.foldl_cons] using h

theorem traversal_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=L) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
    ExecutesIn (.seq peekRow loop) (rows.length*(stepBudget L t d+2)+2)
      (ready base rows acc)
      (ready base [] (rows.foldl (stepValue t a M cache theta) acc)) := by
  intro regs
  obtain ⟨ns,rf,hns,he⟩ := loop_eval t a M cache hz base hready theta acc rows L hL
    hx hz0 hc hw h232 h240 h246 h248 h241 h244 h245 h251 h252 regs
  exact ⟨1+ns,rf,by omega,(peekRow_eval regs base rows acc).seq he⟩

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
