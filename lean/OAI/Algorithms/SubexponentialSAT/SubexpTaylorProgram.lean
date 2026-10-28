import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorSweep
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorOuter
import OAI.Algorithms.SubexponentialSAT.SubexpHornerMachine

namespace OAI.Algorithms

/-! The affine Taylor sweep instantiated with the actual flat quartic
multiply and add programs.  The coefficient loop has fixed finite control. -/

namespace SubexponentialSAT.SubexpTaylorProgram

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpLiftRing SubexpQuarticRing

abbrev arithmetic : Cmd 8 87 :=
  .seq prepareMultiply (.seq SubexpHornerMachine.multiply SubexpHornerMachine.add)

abbrev command : Cmd 8 87 := SubexpTaylorControl.command arithmetic
abbrev program : Program 8 87 (size command + 1) := compiled command 77 77
def shiftProgram := SubexpTaylorOuter.program program
def reversedShiftProgram := SubexpTaylorOuter.reversedProgram program

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Code := Quad (Word (baseWidth p μ))
abbrev flat := @SubexpQuarticFlatMul.flat

theorem arithmetic_eval (t theta : Code p μ) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (regs : Fin 8 → Bool) (w : Words) (a b : Code p μ)
    (hm : w.modulus = M.bits) (hwidth : w.width = width)
    (ht : w.reduction = flat t) (hx : w.point = flat theta)
    (ha : w.accumulator = flat a) (hb : w.coefficient = flat b)
    (hwork : w.work = []) (hl : w.left = []) (hr : w.right = []) :
    ∃ n ≤ 500000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval arithmetic n (state regs w)
        (state regs' {w with
          accumulator := flat (SubexpHornerMachine.stepValue p μ M t theta a b),
          coefficient := []}) := by
  let w1 := {w with accumulator := [], left := w.accumulator, right := w.point}
  let w2 := {w1 with
    left := []
    right := []
    accumulator := flat (SubexpPreparedQuartic.binaryMul p μ M t a theta).1}
  have hp := prepareMultiply_eval regs w hwork hl hr
  obtain ⟨nm, hnm, rm, hmul⟩ := SubexpHornerMachine.multiply_eval p μ M
    (readRegs regs 0 1 none) w1 t a theta hm ht
    (by simpa [w1, hwidth] using hw) ha hx rfl hwork
  obtain ⟨na, hna, ra, hadd⟩ := SubexpHornerMachine.add_eval p μ M rm w2
    (SubexpPreparedQuartic.binaryMul p μ M t a theta).1 b hm
    (by simpa [w2, w1, hwidth] using hw) rfl hb hwork
  refine ⟨6 * w.accumulator.length + 7 * w.point.length + 11 + (nm + na), ?_, ra, ?_⟩
  · rw [ha, hx, SubexpQuarticFlatMul.flat_length, SubexpQuarticFlatMul.flat_length]
    nlinarith [Nat.zero_le (baseWidth p μ), Nat.zero_le ((baseWidth p μ)^2)]
  · have h := hp.seq (hmul.seq hadd)
    simpa only [arithmetic, w1, w2, SubexpHornerMachine.stepValue, hl, hr] using h

def scalarBound (B : ℕ) : ℕ := 500000 * (B + 1)^2

def shiftBound (n B : ℕ) : ℕ :=
  9 * (n * (4 * B)) + n * ((n + 1) * (scalarBound B + 33 * (4 * B) + 27) + 2) + 10

theorem affine_trace (hμ : 0 < μ) (t theta : Code p μ) (width blockWidth : List Bool)
    (hw : width.length = baseWidth p μ) (hblock : blockWidth.length = 4 * baseWidth p μ)
    (regs : Fin 8 → Bool) (Q : List (Code p μ)) (b : Code p μ) :
    ∃ n ≤ Q.length * (scalarBound (baseWidth p μ) + 33 * (4 * baseWidth p μ) + 27) +
      6 * (4 * baseWidth p μ) + 9, ∃ regs',
      Trace program n
        ((state regs (SubexpTaylorControl.ready flat
          (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) Q b [])).withPC
            (some program.entry))
        ((state regs' (SubexpTaylorControl.done
          (SubexpHornerMachine.baseWords p μ M t theta width blockWidth)
          (SubexpTaylorControl.encodeList flat
            (SubexpTaylorControl.sweep (SubexpHornerMachine.stepValue p μ M t theta) b Q)))).withPC none) := by
  have hpos : 0 < 4 * baseWidth p μ := by
    have : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.succ_pos _)
    omega
  obtain ⟨n, hn, rr, hr⟩ := SubexpTaylorSweep.command_eval flat (4 * baseWidth p μ)
    SubexpQuarticFlatMul.flat_length hpos
    (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) hblock
    arithmetic (SubexpHornerMachine.stepValue p μ M t theta) (scalarBound (baseWidth p μ))
    (by
      intro rs w a b hm hw' ht hx ha hb hwork hl hr
      exact arithmetic_eval p μ M t theta width hw rs w a b hm hw' ht hx ha hb hwork hl hr)
    Q b regs
  exact ⟨n + 1, by omega, rr, compiled_halt_trace hr 77 77⟩

theorem shift_trace (hμ : 0 < μ) (t theta : Code p μ) (width blockWidth : List Bool)
    (hw : width.length = baseWidth p μ) (hblock : blockWidth.length = 4 * baseWidth p μ)
    (regs : Fin 8 → Bool) (P : List (Code p μ)) :
    ∃ n ≤ shiftBound P.length (baseWidth p μ), ∃ regs',
      Trace shiftProgram n
        ((SubexpTaylorOuter.outerState regs
          (SubexpTaylorControl.done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) [])
          (SubexpTaylorControl.encodeList flat P)).withPC (some shiftProgram.entry))
        ((SubexpTaylorOuter.outerState regs'
          (SubexpTaylorControl.done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth)
            (SubexpTaylorControl.encodeList flat (SubexpTaylorSemantics.compactShift
              (SubexpHornerMachine.stepValue p μ M t theta) P))) []).withPC none) := by
  have hpos : 0 < 4 * baseWidth p μ := by
    have : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.succ_pos _)
    omega
  exact SubexpTaylorOuter.program_trace flat (4 * baseWidth p μ)
    SubexpQuarticFlatMul.flat_length hpos
    (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) hblock
    program (SubexpHornerMachine.stepValue p μ M t theta) (scalarBound (baseWidth p μ))
    (affine_trace p μ M hμ t theta width blockWidth hw hblock) regs P

theorem shift_value (c : Fin 4 → ZMod (p^μ)) (t theta : Code p μ)
    (ht : t.map (wordValue p μ) = reductionData c) (P : List (Code p μ)) :
    PolynomialAlgorithm.denote
      ((SubexpTaylorSemantics.compactShift (SubexpHornerMachine.stepValue p μ M t theta) P).map
        (SubexpHornerMachine.decode p μ c)) =
      (PolynomialAlgorithm.denote (P.map (SubexpHornerMachine.decode p μ c))).comp
        (Polynomial.X + Polynomial.C (SubexpHornerMachine.decode p μ c theta)) := by
  apply SubexpTaylorSemantics.compactShift_decode
  intro a b
  simp only [SubexpHornerMachine.stepValue, SubexpHornerMachine.decode,
    SubexpPreparedQuartic.binaryAdd_quotient,
    SubexpPreparedQuartic.binaryMul_quotient p μ M c t a theta ht]

theorem reversed_shift_trace (hμ : 0 < μ) (t theta : Code p μ) (width blockWidth : List Bool)
    (hw : width.length = baseWidth p μ) (hblock : blockWidth.length = 4 * baseWidth p μ)
    (regs : Fin 8 → Bool) (P : List (Code p μ)) :
    ∃ n ≤ P.length * ((P.length + 1) *
      (scalarBound (baseWidth p μ) + 33 * (4 * baseWidth p μ) + 27) + 2) + 3,
      ∃ regs', Trace reversedShiftProgram n
        ((SubexpTaylorOuter.outerState regs
          (SubexpTaylorControl.done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) [])
          (SubexpTaylorControl.encodeList flat P).reverse).withPC (some reversedShiftProgram.entry))
        ((SubexpTaylorOuter.outerState regs'
          (SubexpTaylorControl.done (SubexpHornerMachine.baseWords p μ M t theta width blockWidth)
            (SubexpTaylorControl.encodeList flat (SubexpTaylorSemantics.compactShift
              (SubexpHornerMachine.stepValue p μ M t theta) P))) []).withPC none) := by
  have hpos : 0 < 4 * baseWidth p μ := by
    have : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.succ_pos _)
    omega
  exact SubexpTaylorOuter.reversed_program_trace flat (4 * baseWidth p μ)
    SubexpQuarticFlatMul.flat_length hpos
    (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) hblock
    program (SubexpHornerMachine.stepValue p μ M t theta) (scalarBound (baseWidth p μ))
    (affine_trace p μ M hμ t theta width blockWidth hw hblock) regs P

end SubexponentialSAT.SubexpTaylorProgram

end OAI.Algorithms
