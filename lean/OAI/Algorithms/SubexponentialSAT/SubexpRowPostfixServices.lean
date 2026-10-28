import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl

namespace OAI.Algorithms

/-!
# Framed arithmetic calls for source-row postfix expressions

The physical interpreter keeps its operand list on stack 27. These fixed
commands read two framed operands, call a dense polynomial service on
240/241, and frame its result from 244. All temporary stacks are restored;
the caller's remaining operands and every other stack are preserved.
-/

namespace SubexponentialSAT.SubexpRowPostfixServices

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl (Code Store Data ExecutesIn copy clear copy_run clear_run)
open SubexpDenseLiteralPadding (take take_run write write_run reset reset_eval)

local infixr:60 " ;; " => Cmd.seq

/-- Move a runtime word in its original orientation, using the shared copy
scratch stack 120. The source and destination are fixed program ports. -/
def move (src dst : Fin 256) : Code := copy src dst ;; clear src

theorem move_from_update (src dst : Fin 256) (s : Store) (bits : List Bool)
    (hne : src ≠ dst) (hs : src ≠ 120) (hd : (120 : Fin 256) ≠ dst)
    (hsrc : s src = []) (hdst : s dst = []) (htmp : s 120 = []) :
    ExecutesIn (move src dst) (9 * bits.length + 8)
      (Function.update s src bits) (Function.update s dst bits) := by
  let middle := Function.update (Function.update s src bits) dst bits
  have h1 : ExecutesIn (copy src dst) (7 * bits.length + 5)
      (Function.update s src bits) middle := by
    simpa [middle, hne, Ne.symm hne, hdst] using copy_run src dst (Function.update s src bits)
      hne hs hd (by simpa [Ne.symm hs] using htmp)
  have he : Function.update middle src [] = Function.update s dst bits := by
    funext j
    by_cases hj : j = src
    · subst j
      simp [middle, hne, hsrc]
    · simp [middle, Function.update_apply, hj]
  have h2 : ExecutesIn (clear src) (2 * bits.length + 3)
      middle (Function.update s dst bits) := by
    have h := clear_run src middle
    rw [he] at h
    simpa [middle, hne] using h
  simpa only [move, show 7 * bits.length + 5 + (2 * bits.length + 3) =
      9 * bits.length + 8 by omega] using h1.seq h2

def prepared (s : Store) (left right tail : List Bool) : Store :=
  Function.update (Function.update (Function.update s 27 tail) 241 right) 240 left

def prepare : Code := take ;; move 21 241 ;; take ;; move 21 240

theorem prepare_run (s : Store) (left right tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame right ++
      (true :: (Encoding.frame left ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) :
    ExecutesIn prepare (18 * (left.length + right.length) + 34) s
      (prepared s left right tail) := by
  let rest := true :: (Encoding.frame left ++ tail)
  let s1 := Function.update s 27 rest
  let s2 := Function.update s1 241 right
  let s3 := Function.update s2 27 tail
  have h1 := take_run s right rest hin h21 h29
  have h2 := move_from_update 21 241 s1 right (by decide) (by decide) (by decide)
    (by simpa [s1] using h21) (by simpa [s1] using h241) (by simpa [s1] using h120)
  have h3 := take_run s2 left tail (by simp [s2, s1, rest])
    (by simpa [s2, s1] using h21) (by simpa [s2, s1] using h29)
  have h4 := move_from_update 21 240 s3 left (by decide) (by decide) (by decide)
    (by simpa [s3, s2, s1] using h21) (by simpa [s3, s2, s1] using h240)
    (by simpa [s3, s2, s1] using h120)
  have he : Function.update s3 240 left = prepared s left right tail := by
    funext j
    by_cases hj : j = 27 <;> simp [s3, s2, s1, prepared, Function.update_apply, hj]
  rw [he] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | rfl | omega

def finish : Code := clear 240 ;; clear 241 ;;
  SubexpPolynomialServiceControl.transfer 244 29 ;; write

theorem finish_run (s : Store) (left right tail out : List Bool)
    (h29 : s 29 = []) (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = []) :
    ExecutesIn finish (2 * (left.length + right.length) + 8 * out.length + 17)
      (Function.update (prepared s left right tail) 244 out)
      (Function.update s 27 (true :: (Encoding.frame out ++ tail))) := by
  let base := Function.update s 27 tail
  let s1 := Function.update (Function.update base 241 right) 244 out
  let s2 := Function.update base 244 out
  let s3 := Function.update base 29 out.reverse
  have he1 : Function.update (Function.update (prepared s left right tail) 244 out)
      240 [] = s1 := by
    funext j
    by_cases hj : j = 240 <;>
      simp [prepared, s1, base, Function.update_apply, hj, h240]
  have h1 : ExecutesIn (clear 240) (2 * left.length + 3)
      (Function.update (prepared s left right tail) 244 out) s1 := by
    have h := clear_run 240 (Function.update (prepared s left right tail) 244 out)
    rw [he1] at h
    simpa [prepared] using h
  have he2 : Function.update s1 241 [] = s2 := by
    funext j
    by_cases hj : j = 241 <;> simp [s1, s2, base, Function.update_apply, hj, h241]
  have h2 : ExecutesIn (clear 241) (2 * right.length + 3) s1 s2 := by
    have h := clear_run 241 s1
    rw [he2] at h
    simpa [s1] using h
  have he3 : Function.update (Function.update s2 244 []) 29
      ((s2 244).reverse ++ s2 29) = s3 := by
    funext j
    by_cases hj : j = 244 <;> simp [s3, s2, base, Function.update_apply, hj, h29, h244]
  have h3 : ExecutesIn (SubexpPolynomialServiceControl.transfer 244 29)
      (3 * out.length + 3) s2 s3 := by
    have h := SubexpPolynomialServiceControl.transfer_run 244 29 s2 (by decide)
    rw [he3] at h
    simpa [s2] using h
  have he4 : Function.update (Function.update s3 27
      (true :: (Encoding.frame out ++ s3 27))) 29 [] =
      Function.update s 27 (true :: (Encoding.frame out ++ tail)) := by
    funext j
    by_cases hj : j = 29 <;> by_cases hj27 : j = 27 <;>
      simp [s3, base, hj, hj27, h29]
  have h4 := write_run s3 out (by simp [s3])
  rw [he4] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 <;> first | rfl | omega

/-- The supplied arithmetic command is installed as actual finite code. -/
def command (arithmetic : Code) : Code := prepare ;; arithmetic ;; finish ;; reset

def program (arithmetic : Code) := compiled (command arithmetic) 27 27

/-- Exact framing around any checked dense-array arithmetic service.
The service hypothesis is a trace of the inserted command on the actual
prepared stores, and is later discharged by the concrete add/multiply tables. -/
theorem program_runsIn (arithmetic : Code) (K : ℕ) (s : Store)
    (regs : Fin 16 → Bool) (left right tail out : List Bool)
    (hin : s 27 = true :: (Encoding.frame right ++
      (true :: (Encoding.frame left ++ tail))))
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (harithmetic : ExecutesIn arithmetic K (prepared s left right tail)
      (Function.update (prepared s left right tail) 244 out)) :
    RunsIn (program arithmetic)
      (K + 20 * (left.length + right.length) + 8 * out.length + 69)
      ((⟨regs, s⟩ : Data).withPC (some (program arithmetic).entry))
      ((⟨fun _ => false,
        Function.update s 27 (true :: (Encoding.frame out ++ tail))⟩ : Data).withPC none) := by
  have hprepare := prepare_run s left right tail hin h21 h29 h120 h240 h241
  have hfinish := finish_run s left right tail out h29 h240 h241 h244
  obtain ⟨na, ra, hna, hea⟩ := hprepare regs
  obtain ⟨nb, rb, hnb, heb⟩ := harithmetic ra
  obtain ⟨nc, rc, hnc, hec⟩ := hfinish rb
  have hed := reset_eval rc (Function.update s 27 (true :: (Encoding.frame out ++ tail)))
  refine ⟨na + (nb + (nc + 17)) + 1, by omega, ?_⟩
  exact compiled_halt_trace (hea.seq (heb.seq (hec.seq hed))) 27 27

end SubexponentialSAT.SubexpRowPostfixServices

end OAI.Algorithms
