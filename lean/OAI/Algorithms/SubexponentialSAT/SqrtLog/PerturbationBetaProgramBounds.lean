import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramSemantics

namespace OAI.Algorithms

/-! Polynomial native cost, including framing, all skipped rows, and cleanup.
The parser dependency has a fixed16/256 ABI owned by this helper. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

theorem rowsBits_length {t d : ℕ} (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L) :
    (rowsBits rows).length=rows.length*(2*(L*(d*baseWidth 3 t))+2)+1 := by
  induction rows with
  | nil => simp [rowsBits]
  | cons row rows ih =>
    have hl := hL row (by simp)
    have hi := ih (fun r hr => hL r (by simp [hr]))
    simp only [rowsBits,List.map_cons,Encoding.length_encodeList_cons,
      HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length,hl] at *
    rw [hi]
    simp only [List.length_cons]
    ring

def nativeBudget (n L t d : ℕ) : ℕ :=
  7*(n*(2*(L*(d*baseWidth 3 t))+2)+1)+7*n+21*(d*baseWidth 3 t)+25+
    n*(stepBudget L t d+2)+2+(4*(d*baseWidth 3 t)+14)

theorem runBudget_eq (t d L : ℕ) (base : Store) (rows : List (List (Coeff t d) × Bool))
    (theta zero : Coeff t d) (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat zero) (h209 : base 209=RingProgram.flat theta)
    (h211 : (base 211).length=d*baseWidth 3 t) :
    runBudget base rows.length L t d=nativeBudget rows.length L t d := by
  simp only [runBudget,initBudget,h205,h206,h207,h209,List.length_map,
    RingProgram.flat_length,h211,rowsBits_length rows L hL,nativeBudget]
  ring

theorem nativeBudget_polynomial (n L t d : ℕ) :
    nativeBudget n L t d ≤ 1000000*(n+1)*(L+1)*(d+1)^3*(baseWidth 3 t+1)^2 := by
  have hm := HornerProgram.modelBudget_polynomial L t d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  have hsum := Nat.mul_le_mul_left n (Nat.add_le_add hm ha)
  unfold nativeBudget stepBudget selectedBudget
  ring_nf at *
  omega

/-- Direct caller-facing bound after accounting for the actual master tapes. -/
theorem runBudget_polynomial (t d L : ℕ) (base : Store)
    (rows : List (List (Coeff t d) × Bool)) (theta zero : Coeff t d)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat zero) (h209 : base 209=RingProgram.flat theta)
    (h211 : (base 211).length=d*baseWidth 3 t) :
    runBudget base rows.length L t d ≤
      1000000*(rows.length+1)*(L+1)*(d+1)^3*(baseWidth 3 t+1)^2 := by
  rw [runBudget_eq t d L base rows theta zero hL h205 h206 h207 h209 h211]
  exact nativeBudget_polynomial rows.length L t d

/-- The single fixed finite machine has polynomial native cost before its
constant primitive-simulation overhead. -/
theorem betaMachine_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h209 : base 209=RingProgram.flat theta)
    (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
    (he : WorkEmpty base) (regs : Fin 16 → Bool) :
    ∃ out rf, Computation.RunsIn (primitive betaMachine).step
      (primitiveOverhead betaMachine*
        (1000000*(rows.length+1)*(L+1)*(d+1)^3*(baseWidth 3 t+1)^2+1))
      (primitiveCfg betaMachine ((⟨regs,base⟩ : Data).withPC (some betaMachine.entry)))
      (primitiveCfg betaMachine
        ((⟨rf,Function.update base 220 (RingProgram.flat out)⟩ : Data).withPC none)) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  obtain ⟨out,rf,hrun,hval⟩ := betaMachine_correct t ht hd a M cache hz base hready theta rows L hL
    h205 h206 h207 h209 h210 h211 he regs
  refine ⟨out,rf,?_,hval⟩
  have hb := runBudget_eq t d L base rows theta _ hL h205 h206 h207 h209 h211
  rw [hb] at hrun
  exact (BitProgram.primitive_execution betaMachine hrun).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (nativeBudget_polynomial rows.length L t d) 1))

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
