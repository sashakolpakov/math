import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramMatrixRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerResources
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramCostPolynomial

namespace OAI.Algorithms

/-! All-incidence-row matrix and signed-bucket cost. The literal row count D
is retained throughout; no rank bound is substituted into serialization. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem forallTwo_mem_right {A B : Type*} {R : A → B → Prop} {xs : List A} {ys : List B}
    (h : List.Forall₂ R xs ys) (y : B) (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | @cons a b xs ys hab ht ih =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a,by simp,hab⟩
      · obtain ⟨x,hx,hr⟩ := ih hy
        exact ⟨x,by simp [hx],hr⟩

 theorem matrix_pair_bounds {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∀ row ∈ rows, BucketProgram.preWordsBounded B row := by
  intro row hrow
  obtain ⟨j,hj,hrel⟩ := forallTwo_mem_right hr row hrow
  intro p hp
  obtain ⟨v,hv,hpair⟩ := forallTwo_mem_right hrel p hp
  have h := hpair.2
  dsimp [LayoutMatrixProgram.pairLength] at h
  exact ⟨by omega,by omega⟩

 theorem matrix_command_cost (T B D n s : ℕ) (js : List ℕ)
    (hjs : ∀ v∈js,v < n) (hT : T ≤ s) (hB : B ≤ s) (hD : D ≤ s)
    (hn : n ≤ s) (hh : js.length ≤ s) (hs : 1 ≤ s) :
    LayoutMatrixProgram.commandCost T B D n js ≤ 1000*s^3 := by
  apply (LayoutMatrixProgram.commandCost_le_explicit T B D n js
    (fun v hv => (hjs v hv).le)).trans
  calc
    _ ≤ 19*(1+(2*s+2)*s)+12+
      s*(9*s+7*(1+(2*s+2)*s)+s*(s+24*s+8*s+45)+27) := by gcongr
    _ ≤ 1000*s^3 := by
      have h12 : s ≤ s^2 := by nlinarith only [hs]
      have h23 : s^2 ≤ s^3 := pow_le_pow_right₀ hs (by decide)
      nlinarith only [hs,h12,h23]

 def matrixSize (W : List Bool) (T B D n h : ℕ) := T+B+D+n+h+2*W.length+2
 def matrixEnvelope (W : List Bool) (T B D n h : ℕ) :=
   200000000*(2^h+1)^2*(matrixSize W T B D n h)^6

 theorem matrix_native_cost (W : List Bool) (T B D n : ℕ) (js : List ℕ)
    (rows : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows shifted)
    (hjs : ∀ v∈js,v < n) :
    LayoutMatrixProgram.commandCost T B D n js+BucketProgram.preMatrixCost W rows+
      BucketProgram.Controller.cost W shifted js n js.length+3 ≤
        matrixEnvelope W T B D n js.length := by
  let s := matrixSize W T B D n js.length
  have hs : 1 ≤ s := by dsimp [s,matrixSize]; omega
  have hc := matrix_command_cost T B D n s js hjs
    (by dsimp [s,matrixSize]; omega) (by dsimp [s,matrixSize]; omega)
    (by dsimp [s,matrixSize]; omega) (by dsimp [s,matrixSize]; omega)
    (by dsimp [s,matrixSize]; omega) hs
  obtain ⟨hrows,hw⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hb := matrix_pair_bounds hr
  have hpre := BucketProgram.Controller.Resources.preprocess_controller_cost_le W rows shifted js n
    js.length (B+W.length) hy (by omega) hw
    (by intro row hrow p hp; obtain ⟨h1,h2⟩ := hb row hrow p hp; exact ⟨by omega,by omega⟩)
    rfl hjs
  rw [hrows] at hpre
  have ht := BucketProgram.Cost.signedTotal_coarse W js.length D (B+W.length) n
  have hbase : js.length+D+(B+W.length)+n+W.length+2 ≤ s := by dsimp [s,matrixSize]; omega
  have ht' : BucketProgram.Cost.signedTotal W js.length D (B+W.length) n ≤
      101358497*(2^js.length+1)^2*s^6 := ht.trans (by gcongr)
  have h36 : s^3 ≤ s^6 := pow_le_pow_right₀ hs (by decide)
  have hexp : 1 ≤ (2^js.length+1)^2 := Nat.one_le_pow _ _
    (Nat.succ_le_succ (Nat.zero_le ((2:ℕ)^js.length)))
  have hone : 1 ≤ s^6 := one_le_pow₀ hs
  have hscale : s^6 ≤ (2^js.length+1)^2*s^6 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (s^6) hexp
  change _ ≤ 200000000*(2^js.length+1)^2*s^6
  nlinarith only [hc,hpre,ht',h36,hscale,hone]

 theorem matrix_post_wordBound (entry : Cmd 16 256) (a : Data) (D n T B M : ℕ)
    (js : List ℕ) (rows : List (List LayoutMatrixProgram.Pair))
    (shifted : List (List (List Bool))) (mb : State 16 288)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) rows shifted)
    (hjs : ∀ v∈js,v < n)
    (hi : WordBound M (LayoutMatrixProgram.initialState (matrixBase a)
      (prepared (by decide) matrixInputs a).regs D))
    (he : MatrixExecution entry a D n js T B rows shifted mb) :
    WordBound (M+matrixEnvelope (a.stacks 141) T B D n js.length) mb := by
  exact wordBound_mono (runsIn_wordBound he hi)
    (Nat.add_le_add_left (matrix_native_cost (a.stacks 141) T B D n js rows shifted Rel hr hy hjs) M)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
