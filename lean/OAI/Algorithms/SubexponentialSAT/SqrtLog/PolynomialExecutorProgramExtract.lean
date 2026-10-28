import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixServices
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixFrames

namespace OAI.Algorithms

/-! Native removal of the final postfix frame. This exposes the plain
constant-coefficient-first array required by perturbation and interpolation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

local infixr:60 " ;; " => Cmd.seq

def extract : Code := SubexpDenseLiteralPadding.take ;;
  SubexpRowPostfixServices.move 21 240 ;; clear 27 ;; clear 28

theorem extract_run (s : Store) (bits : List Bool)
    (h27 : s 27 = true :: (Encoding.frame bits ++ [false])) (h28 : s 28 = [true])
    (h21 : s 21 = []) (h29 : s 29 = []) (h120 : s 120 = []) (h240 : s 240 = []) :
    ExecutesIn extract (18*bits.length+27) s
      (Function.update (Function.update (Function.update s 27 []) 240 bits) 28 []) := by
  let s1 := Function.update s 27 [false]
  let s2 := Function.update s1 240 bits
  let s3 := Function.update (Function.update s 27 []) 240 bits
  have ht := SubexpDenseLiteralPadding.take_run s bits [false] h27 h21 h29
  have hm := SubexpRowPostfixServices.move_from_update 21 240 s1 bits
    (by decide) (by decide) (by decide)
    (by simp [s1,h21]) (by simp [s1,h240]) (by simp [s1,h120])
  have hc1 : ExecutesIn (clear 27) 5 s2 s3 := by
    have h := clear_run 27 s2
    have he : Function.update s2 27 [] = s3 := by
      funext i
      by_cases hi : i = 27 <;> simp [s1,s2,s3,Function.update_apply,hi]
    rw [he] at h
    simpa [s2,s1] using h
  have hc2 : ExecutesIn (clear 28) 5 s3 (Function.update s3 28 []) := by
    simpa [s3,h28] using clear_run 28 s3
  have h := ht.seq (hm.seq (hc1.seq hc2))
  convert h using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
