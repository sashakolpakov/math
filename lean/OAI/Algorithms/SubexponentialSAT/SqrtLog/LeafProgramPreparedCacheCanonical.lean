import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

/-! The integer layout cache has a fixed length for every word. Its exact
numeric specification therefore determines its physical bytes, independently
of the caller's registers and scratch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
noncomputable section

private theorem lists_eq_of_width_value (width : ℕ) (xs ys : List (List Bool))
    (hx : ∀ x∈xs,x.length=width) (hy : ∀ y∈ys,y.length=width)
    (hv : xs.map BinaryArithmetic.toNat=ys.map BinaryArithmetic.toNat) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hv
  | cons x xs ih =>
    cases ys with
    | nil => simp at hv
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at hv
      have hxy := SubexpModulusConstruction.bits_eq_of_length_of_value x y
        ((hx x (by simp)).trans (hy y (by simp)).symm) hv.1
      subst y
      exact congrArg (List.cons x) (ih ys (fun z hz=>hx z (by simp [hz]))
        (fun z hz=>hy z (by simp [hz])) hv.2)

 theorem cacheCorrect_unique {height R width : List Bool} {xs ys : List (List Bool)}
    (hx : CacheCorrect height R width xs) (hy : CacheCorrect height R width ys) : xs=ys :=
  lists_eq_of_width_value width.length xs ys hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)

 theorem cacheWords_exists (s : Native.Inputs) :
    ∃ words,CacheCorrect s.height (unary s.R) s.width words := by
  obtain ⟨rf,words,_,hlen,hwidth,hvalue,_⟩ :=
    LayoutProgram.IntegerCache.program_runsIn (fun _=>false) s.height (unary s.R) s.width
      (by simpa only [unary,List.length_replicate] using s.width_boot)
  exact ⟨words,hlen,hwidth,hvalue⟩

 def cacheWords (s : Native.Inputs) : List (List Bool) := (cacheWords_exists s).choose

 theorem cacheWords_correct (s : Native.Inputs) :
    CacheCorrect s.height (unary s.R) s.width (cacheWords s) := (cacheWords_exists s).choose_spec

 theorem cacheWords_eq (s : Native.Inputs) {words : List (List Bool)}
    (hc : CacheCorrect s.height (unary s.R) s.width words) : words=cacheWords s :=
  cacheCorrect_unique hc (cacheWords_correct s)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
