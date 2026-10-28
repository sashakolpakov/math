import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramSelected

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

abbrev Coeff (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def rowsBits {t d : ℕ} (rows : List (List (Coeff t d) × Bool)) : List Bool :=
  Encoding.encodeList (HornerProgram.encodePolynomial RingProgram.flat) (rows.map Prod.fst)

def ready {t d : ℕ} (base : Store) (rows : List (List (Coeff t d) × Bool))
    (acc : Coeff t d) : Store :=
  Function.update (Function.update (Function.update base 230 (rowsBits rows))
    231 (rows.map Prod.snd)) 220 (RingProgram.flat acc)

theorem ready_lowFrame {t d : ℕ} (base : Store) (rows : List (List (Coeff t d) × Bool))
    (acc : Coeff t d) : LowFrame base (ready base rows acc) :=
  lowFrame_update (lowFrame_update (lowFrame_update (lowFrame_refl base)
    230 (by decide) _) 231 (by decide) _) 220 (by decide) _

def stepValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta acc : Coeff t d) (row : List (Coeff t d) × Bool) : Coeff t d :=
  if row.2 then nextValue t a M cache row.1 theta acc else acc

def stepBudget (L t d : ℕ) : ℕ :=
  11*(L*(d*baseWidth 3 t))+selectedBudget L t d+13

theorem step_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (P : List (Coeff t d)) (b : Bool)
    (rows : List (List (Coeff t d) × Bool))
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=P.length) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
    ExecutesIn step (stepBudget P.length t d) (ready base ((P,b)::rows) acc)
      (ready base rows (stepValue t a M cache theta acc (P,b))) := by
  let s := ready base ((P,b)::rows) acc
  let sr := Function.update (Function.update s 230 (rowsBits rows)) 246
    (HornerProgram.encodePolynomial RingProgram.flat P)
  let sp := Function.update sr 231 (rows.map Prod.snd)
  have hr : ExecutesIn readRow (9*(P.length*(d*baseWidth 3 t))+8) s sr := by
    simpa only [HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length] using
      readRow_run s (HornerProgram.encodePolynomial RingProgram.flat P) (rowsBits rows)
        (by simp [s,ready,rowsBits,Encoding.encodeList])
        (by simp [s,ready,h232]) (by simp [s,ready,h246])
  have hf : LowFrame base sp := lowFrame_update (lowFrame_update
    (lowFrame_update (ready_lowFrame base ((P,b)::rows) acc) 230 (by decide) _)
      246 (by decide) _) 231 (by decide) _
  have hbranch : ExecutesIn (if b then selected else skip)
      (selectedBudget P.length t d+2*(P.length*(d*baseWidth 3 t))+3) sp
      (ready base rows (stepValue t a M cache theta acc (P,b))) := by
    cases b with
    | false =>
      have he : Function.update sp 246 []=ready base rows acc := by
        funext i
        by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=246 <;>
          by_cases h3 : i=220 <;>
          simp [sp,sr,s,ready,h0,h1,h2,h3,h246]
      have h := clear_run 246 sp
      rw [he] at h
      have hp : (sp 246).length=P.length*(d*baseWidth 3 t) := by
        simp [sp,sr,HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length]
      simpa only [Bool.false_eq_true,ite_false,stepValue,skip,hp] using
        h.mono (by omega)
    | true =>
      have h := selected_run t a M cache hz sp (hready.frame hf) P theta acc
        (by simp [sp,sr]) (by simp [sp,sr,s,ready,hx]) (by simp [sp,sr,s,ready])
        (by simp [sp,sr,s,ready,hz0]) (by simp [sp,sr,s,ready,hc])
        (by simp [sp,sr,s,ready,hw]) (by simp [sp,sr,s,ready,h240])
        (by simp [sp,sr,s,ready,h248]) (by simp [sp,sr,s,ready,h241])
        (by simp [sp,sr,s,ready,h244]) (by simp [sp,sr,s,ready,h245])
        (by simp [sp,sr,s,ready,h251]) (by simp [sp,sr,s,ready,h252])
      have he : Function.update (Function.update sp 246 []) 220
          (RingProgram.flat (nextValue t a M cache P theta acc)) =
          ready base rows (nextValue t a M cache P theta acc) := by
        funext i
        by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=246 <;>
          by_cases h3 : i=220 <;>
          simp [sp,sr,s,ready,h0,h1,h2,h3,h246]
      rw [he] at h
      simpa [stepValue] using h.mono (by omega)
  intro regs
  obtain ⟨nr,rr,hnr,her⟩ := hr regs
  let rp := readRegs rr 0 1 (some b)
  have hep : Eval popChoice 1 (⟨rr,sr⟩ : Data) (⟨rp,sp⟩ : Data) := by
    have hb : sr 231=b::rows.map Prod.snd := by simp [sr,s,ready]
    simpa [popChoice,rp,sp,hb,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      (Eval.base (StructuredProgram.Eval.atom (.pop (231 : Fin 256) (0 : Fin 16) 1)
        (⟨rr,sr⟩ : Data)))
  obtain ⟨nb,rb,hnb,heb⟩ := hbranch rp
  have heif : Eval (.ite 0 selected skip) (nb+1) (⟨rp,sp⟩ : Data)
      (⟨rb,ready base rows (stepValue t a M cache theta acc (P,b))⟩ : Data) := by
    cases b
    · exact Eval.ite_false (by simp [rp,readRegs]) heb
    · exact Eval.ite_true (by simp [rp,readRegs]) heb
  refine ⟨nr+(1+(nb+1)),rb,?_,her.seq (hep.seq heif)⟩
  dsimp [stepBudget]
  omega

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
