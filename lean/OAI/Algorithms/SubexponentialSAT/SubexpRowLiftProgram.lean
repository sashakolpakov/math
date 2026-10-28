import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientLiftArray
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding

namespace OAI.Algorithms

/-! The physical final stage of a source-row computation: remove its single
framed dense result and lift each coefficient to the target modulus. The
output on 87 is the complete flat row reversed, as required by TaylorRow. -/

namespace SubexponentialSAT.SubexpRowLiftProgram

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Code Store Data ExecutesIn clear clear_run)

local infixr:60 " ;; " => Cmd.seq

def liftRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def liftPorts : Fin 20 → Fin 256 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 21, 87, 10, 74, 12, 13, 14, 15, 16, 17, 18, 19]

theorem liftRegs_injective : Function.Injective liftRegs := Fin.castAdd_injective _ _
theorem liftPorts_injective : Function.Injective liftPorts := by decide

def lift : Code := .call (ProgramLinking.liftProgram
  SubexpCoefficientLiftArray.program liftRegs liftPorts)

private theorem lifted_stacks (regs rf : Fin 8 → Bool)
    (modulus input output sw tw : List Bool) (frame : Fin 6 → List Bool) :
    (SubexpFlatLift.ready rf modulus [] output sw tw frame).stacks =
      Function.update (Function.update
        (SubexpFlatLift.ready regs modulus input [] sw tw frame).stacks 8 []) 9 output := by
  funext i
  simp only [SubexpFlatLift.ready, SubexpFlatLift.state,
    SubexpFlatLift.stackArray, Function.update_apply]
  refine Fin.addCases (m := 14) (n := 6) ?_ ?_ i
  · intro j
    fin_cases j <;> simp [Fin.addCases, Fin.coe_ofNat_eq_mod]
  · intro j
    have h8 : Fin.natAdd 14 j ≠ (8 : Fin 20) := by
      intro h
      have hv := congrArg Fin.val h
      change 14 + j.val = 8 at hv
      omega
    have h9 : Fin.natAdd 14 j ≠ (9 : Fin 20) := by
      intro h
      have hv := congrArg Fin.val h
      change 14 + j.val = 9 at hv
      omega
    simp [Fin.addCases, h8, h9]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

theorem lift_run (hμ : 0 < μ) (s : Store)
    (P : List (Quad (Word (baseWidth p 1)))) (sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hstore : ∀ i, s (liftPorts i) =
      (SubexpFlatLift.ready (fun _ => false) M.bits
        (SubexpCoefficientLiftArray.encodeArray P) [] sw tw frame).stacks i) :
    ExecutesIn lift
      (3000 * (P.length + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2) s
      (Function.update (Function.update s 21 []) 87
        (SubexpCoefficientLiftArray.encodeArray
          (SubexpCoefficientLiftArray.liftedArray p μ M P)).reverse) := by
  intro regs
  obtain ⟨rf, n, hn, ht⟩ := SubexpCoefficientLiftArray.program_runs p μ M hμ
    (regs ∘ liftRegs) P sw tw frame hb hB
  let a := SubexpFlatLift.ready (regs ∘ liftRegs) M.bits
    (SubexpCoefficientLiftArray.encodeArray P) [] sw tw frame
  let out := (SubexpCoefficientLiftArray.encodeArray
    (SubexpCoefficientLiftArray.liftedArray p μ M P)).reverse
  let b := SubexpFlatLift.ready rf M.bits [] out sw tw frame
  have hs : Function.extend liftPorts a.stacks s = s := by
    funext i
    by_cases hi : ∃ j, liftPorts j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [liftPorts_injective.extend_apply]
      exact (hstore j).symm
    · exact Function.extend_apply' _ _ _ hi
  have hr : Function.extend liftRegs (regs ∘ liftRegs) regs = regs := by
    funext i
    by_cases hi : ∃ j, liftRegs j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [liftRegs_injective.extend_apply]
      rfl
    · exact Function.extend_apply' _ _ _ hi
  have hin : embedState liftRegs liftPorts (⟨regs, s⟩ : Data) a = ⟨regs, s⟩ := by
    change StructuredProgram.State.mk (Function.extend liftRegs (regs ∘ liftRegs) regs)
      (Function.extend liftPorts a.stacks s) = _
    rw [hr, hs]
  have hout : embedState liftRegs liftPorts (⟨regs, s⟩ : Data) b =
      (⟨Function.extend liftRegs rf regs,
        Function.update (Function.update s 21 []) 87 out⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk _)
    change Function.extend liftPorts b.stacks s = _
    rw [show b.stacks = Function.update (Function.update a.stacks 8 []) 9 out from
      lifted_stacks _ _ _ _ _ _ _ _,
      ProgramLinking.extend_update liftPorts_injective,
      ProgramLinking.extend_update liftPorts_injective, hs]
    rfl
  have he := eval_call_lifted SubexpCoefficientLiftArray.program liftRegs liftPorts
    (⟨regs, s⟩ : Data) liftRegs_injective liftPorts_injective (a := a) (b := b) ht
  exact ⟨n, Function.extend liftRegs rf regs, hn,
    by simpa only [lift, hin, hout, out] using he⟩

def extract : Code := SubexpDenseLiteralPadding.take ;; clear 27 ;; clear 28

def extracted (s : Store) (bits : List Bool) : Store :=
  Function.update (Function.update (Function.update s 27 []) 21 bits) 28 []

theorem extract_run (s : Store) (bits : List Bool)
    (hin : s 27 = true :: (Encoding.frame bits ++ [false]))
    (hdepth : s 28 = [true]) (h21 : s 21 = []) (h29 : s 29 = []) :
    ExecutesIn extract (9 * bits.length + 19) s (extracted s bits) := by
  let s1 := Function.update (Function.update s 27 [false]) 21 bits
  let s2 := Function.update (Function.update s 27 []) 21 bits
  have h1 := SubexpDenseLiteralPadding.take_run s bits [false] hin h21 h29
  have he : Function.update s1 27 [] = s2 := by
    funext i
    by_cases hi : i = 27 <;> simp [s1, s2, hi, Function.update_apply]
  have h2 : ExecutesIn (clear 27) 5 s1 s2 := by
    have h := clear_run 27 s1
    rw [he] at h
    simpa [s1] using h
  have h3 : ExecutesIn (clear 28) 5 s2 (extracted s bits) := by
    simpa [s2, extracted, hdepth] using clear_run 28 s2
  have h := h1.seq (h2.seq h3)
  have hcost : 9 * bits.length + 9 + (5 + 5) = 9 * bits.length + 19 := by
    omega
  rw [hcost] at h
  exact h

def command : Code := extract ;; lift
def program := compiled command 27 87

theorem program_run (hμ : 0 < μ) (s : Store) (regs : Fin 16 → Bool)
    (P : List (Quad (Word (baseWidth p 1)))) (sw tw : List Bool)
    (frame : Fin 6 → List Bool)
    (hb : sw.length = baseWidth p 1) (hB : tw.length = baseWidth p μ)
    (hin : s 27 = true :: (Encoding.frame (SubexpCoefficientLiftArray.encodeArray P) ++ [false]))
    (hdepth : s 28 = [true]) (h21 : s 21 = []) (h29 : s 29 = [])
    (hstore : ∀ i, extracted s (SubexpCoefficientLiftArray.encodeArray P) (liftPorts i) =
      (SubexpFlatLift.ready (fun _ => false) M.bits
        (SubexpCoefficientLiftArray.encodeArray P) [] sw tw frame).stacks i) :
    ∃ rf, RunsIn program
      (9 * (SubexpCoefficientLiftArray.encodeArray P).length + 20 +
        3000 * (P.length + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2)
      ((⟨regs, s⟩ : Data).withPC (some program.entry))
      ((⟨rf, Function.update
        (Function.update (extracted s (SubexpCoefficientLiftArray.encodeArray P)) 21 []) 87
        (SubexpCoefficientLiftArray.encodeArray
          (SubexpCoefficientLiftArray.liftedArray p μ M P)).reverse⟩ : Data).withPC none) := by
  obtain ⟨n, ra, hn, he⟩ := extract_run s (SubexpCoefficientLiftArray.encodeArray P)
    hin hdepth h21 h29 regs
  obtain ⟨m, rb, hm, hf⟩ := lift_run p μ M hμ
    (extracted s (SubexpCoefficientLiftArray.encodeArray P)) P sw tw frame hb hB hstore ra
  exact ⟨rb, n + m + 1, by omega, compiled_halt_trace (he.seq hf) 27 87⟩

end SubexponentialSAT.SubexpRowLiftProgram

end OAI.Algorithms
