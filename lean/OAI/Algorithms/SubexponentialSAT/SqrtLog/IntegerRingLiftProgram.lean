import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCall
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-! A fixed little-endian binary-to-ring scanner.  No natural-number value is
used by the program: each input bit conditionally adds the current place and
then doubles that place.  Arithmetic is supplied by finite native commands;
the concrete RingModel instantiation is in IntegerRingLiftProgramModel. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl
  callAt callAt_run CachePort)

def scan {C : Type*} (add : C → C → C) : List Bool → C → C → C × C
  | [], a, p => (a, p)
  | b :: bs, a, p => scan add bs (if b then add a p else a) (add p p)

theorem scan_decode {C A : Type*} [Ring A] (decode : C → A)
    (add : C → C → C) (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (bs : List Bool) (a p : C) :
    decode (scan add bs a p).1 = decode a + (BinaryArithmetic.toNat bs : A) * decode p := by
  induction bs generalizing a p with
  | nil => simp [scan]
  | cons b bs ih =>
    cases b <;> simp [scan, ih, ha, BinaryArithmetic.toNat] <;> noncomm_ring

def bitPorts : UnaryForPrograms.Ports 16 256 := ⟨246, 0, 1⟩

def bitStep (add : Code) : Code :=
  .seq (.ite 0 (callAt add 247 248 247) (.base .skip))
    (callAt add 248 248 248)

def scanCommand (add : Code) : Code := UnaryForPrograms.forCmd bitPorts (bitStep add)

def scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) : Store :=
  Function.update (Function.update (Function.update base 246 bs) 247 (encode a)) 248 (encode p)

def Clean (s : Store) : Prop :=
  s 120 = [] ∧ s 240 = [] ∧ s 241 = [] ∧ s 244 = [] ∧ s 245 = []

theorem clean_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) (h : Clean base) : Clean (scanState base encode bs a p) := by
  simpa [Clean, scanState] using h

theorem frame_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) : LowFrame base (scanState base encode bs a p) :=
  lowFrame_update (lowFrame_update (lowFrame_update (lowFrame_refl base)
    246 (by decide) _) 247 (by decide) _) 248 (by decide) _

theorem bitStep_eval {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (a p : C) (b : Bool) (hf : LowFrame base s) (hc : Clean s)
    (hacc : s 247 = encode a) (hplace : s 248 = encode p)
    (regs : Fin 16 → Bool) (hb : regs 0 = b) :
    ∃ n rf, n ≤ 2 * (K + 40 * W + 50) + 1 ∧
      Eval (bitStep add) n (⟨regs, s⟩ : Data)
        (⟨rf, Function.update (Function.update s 247 (encode (if b then op a p else a)))
          248 (encode (op p p))⟩ : Data) := by
  let a' := if b then op a p else a
  let s1 := Function.update s 247 (encode a')
  have hfirst : ∃ n rf, n ≤ K + 40 * W + 51 ∧
      Eval (.ite 0 (callAt add 247 248 247) (.base .skip)) n
        (⟨regs, s⟩ : Data) (⟨rf, s1⟩ : Data) := by
    cases b with
    | false =>
      have he : s1 = s := by simp [s1, a', ← hacc]
      refine ⟨1, regs, by omega, ?_⟩
      rw [he]
      exact .ite_false hb (.base (.skip _))
    | true =>
      obtain ⟨n, rf, hn, he⟩ := callAt_run base encode add op K W ha hw s a p
        247 248 247 (by unfold CachePort; decide) (by unfold CachePort; decide)
        (by unfold CachePort; decide) hf hacc hplace
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
        (by simpa [hacc] using hw a) regs
      exact ⟨n+1, rf, by omega, .ite_true hb he⟩
  obtain ⟨n1, r1, hn1, h1⟩ := hfirst
  have hf1 : LowFrame base s1 := lowFrame_update hf 247 (by decide) _
  have hc1 : Clean s1 := by simpa [s1, Clean] using hc
  obtain ⟨n2, r2, hn2, h2⟩ := callAt_run base encode add op K W ha hw s1 p p
    248 248 248 (by unfold CachePort; decide) (by unfold CachePort; decide)
    (by unfold CachePort; decide) hf1
    (by simp [s1, hplace]) (by simp [s1, hplace])
    hc1.1 hc1.2.1 hc1.2.2.1 hc1.2.2.2.1 hc1.2.2.2.2
    (by simpa [s1, hplace] using hw p) r1
  exact ⟨n1+n2, r2, by omega, h1.seq h2⟩

theorem popped_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped bitPorts (⟨regs, scanState base encode bs a p⟩ : Data) =
      (⟨readRegs regs 0 1 bs.head?, scanState base encode bs.tail a p⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, bitPorts, scanState]
  · funext i
    by_cases h246 : i = 246 <;> by_cases h247 : i = 247 <;> by_cases h248 : i = 248 <;>
      simp [UnaryForPrograms.popped, bitPorts, scanState, h246, h247, h248]

theorem scan_visits {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (hc : Clean base) (bs : List Bool) (a p : C) (regs : Fin 16 → Bool) :
    ∃ costs n rf, n ≤ bs.length * (2 * (K + 40 * W + 50) + 3) + 2 ∧
      UnaryForPrograms.Visits bitPorts (bitStep add) costs n
        (⟨regs, scanState base encode bs a p⟩ : Data)
        (⟨rf, scanState base encode [] (scan op bs a p).1 (scan op bs a p).2⟩ : Data) := by
  induction bs generalizing a p regs with
  | nil =>
    refine ⟨[], 2, readRegs regs 0 1 none, by simp, ?_⟩
    simpa only [popped_scanState, List.head?_nil, List.tail_nil, scan] using
      UnaryForPrograms.Visits.done (p := bitPorts) (body := bitStep add)
        (⟨regs, scanState base encode [] a p⟩ : Data) (by simp [scanState, bitPorts])
  | cons b bs ih =>
    let r0 := readRegs regs 0 1 (some b)
    obtain ⟨nb, rb, hnb, hb⟩ := bitStep_eval base encode add op K W ha hw
      (scanState base encode bs a p) a p b (frame_scanState base encode bs a p)
      (clean_scanState base encode bs a p hc) (by simp [scanState])
      (by simp [scanState]) r0 (by simp [r0, readRegs])
    have hs : Function.update (Function.update (scanState base encode bs a p)
        247 (encode (if b then op a p else a))) 248 (encode (op p p)) =
        scanState base encode bs (if b then op a p else a) (op p p) := by
      funext i
      by_cases h247 : i = 247 <;> by_cases h248 : i = 248 <;>
        simp [scanState, Function.update_apply, h247, h248]
    rw [hs] at hb
    obtain ⟨costs, nt, rt, hnt, ht⟩ := ih (if b then op a p else a) (op p p) rb
    refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have h := UnaryForPrograms.Visits.step (p := bitPorts) (body := bitStep add)
        (d := (⟨regs, scanState base encode (b :: bs) a p⟩ : Data))
        (by simp [scanState, bitPorts])
        (by simpa only [popped_scanState, List.head?_cons, List.tail_cons, r0] using hb)
        (by simp [scanState, bitPorts, UnaryForPrograms.popped]) ht
      simpa only [scan] using h

theorem scanCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (hc : Clean base) (bs : List Bool) (a p : C) :
    ExecutesIn (scanCommand add) (bs.length * (2 * (K + 40 * W + 50) + 3) + 2)
      (scanState base encode bs a p)
      (scanState base encode [] (scan op bs a p).1 (scan op bs a p).2) := by
  intro regs
  obtain ⟨costs, n, rf, hn, he⟩ := scan_visits base encode add op K W ha hw hc bs a p regs
  exact ⟨n, rf, hn, he.eval⟩

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
