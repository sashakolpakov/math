import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoaderCore
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeInputs

/-! Source-parameter bounds for the full key produced from an actual shifted
incidence matrix. Every incidence row and every retained coefficient is charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

/-- Serialized full matrix, with the actual incidence count `D`. -/
def matrixBound (n D B L : ℕ) : ℕ := D*(12*n*(B+L)+6*n+1)

def keyCostBound (n D B L : ℕ) : ℕ :=
  let R := matrixBound n D B L
  7*R+D*(BucketProgram.signatureRowBound (List.replicate L false) n R+2)+8

def keySpaceBound (n D B L : ℕ) : ℕ :=
  16*(L+n+matrixBound n D B L)+keyCostBound n D B L+1

/-- A member word is physically contained in its framed serialization. -/
theorem member_word_length_le {xs : List (List Bool)} {x : List Bool} (hx : x ∈ xs) :
    x.length ≤ (words xs).length := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨x,hx,rfl⟩ :
    x.length ∈ xs.map List.length)
  rw [BucketProgram.preWords_length]
  omega

theorem coefficient_length_le {ys : List (List (List Bool))}
    {row : List (List Bool)} {x : List Bool} (hrow : row ∈ ys) (hx : x ∈ row) :
    x.length ≤ (words (ys.map words)).length :=
  (member_word_length_le hx).trans
    (member_word_length_le (List.mem_map.mpr ⟨row,hrow,rfl⟩))

theorem matrix_length_le (W : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) :
    (words (ys.map words)).length ≤ matrixBound n D B L := by
  apply (SignatureHeadLoader.shifted_matrix_word_length W hr hy).trans
  unfold matrixBound
  gcongr

theorem coefficient_bound (W : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) :
    ∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixBound n D B L := by
  intro row hrow x hx
  exact (coefficient_length_le hrow hx).trans (matrix_length_le W hr hy hn hW)

theorem key_cost_le (W bits : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) (hbits : bits.length=js.length) :
    AttainedSignatureProgram.cost W bits ys ≤ keyCostBound n D B L := by
  obtain ⟨hraw,hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hrows : ys.length=D := hy.length_eq.symm.trans hraw
  have hwidth : ∀ row ∈ ys,row.length=bits.length := by
    rw [hbits]
    exact BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  have hm := matrix_length_le W hr hy hn hW
  have hc := AttainedSignatureProgram.cost_le W bits ys (matrixBound n D B L)
    hwidth (coefficient_bound W hr hy hn hW)
  have hb : bits.length ≤ n := hbits ▸ hn
  have hs : BucketProgram.signatureRowBound W bits.length (matrixBound n D B L) ≤       BucketProgram.signatureRowBound (List.replicate L false) n (matrixBound n D B L) := by
    unfold BucketProgram.signatureRowBound BucketProgram.rowCostBound BucketProgram.widthBound
    simp only [List.length_replicate]
    gcongr
  rw [hrows] at hc
  exact hc.trans (by dsimp [keyCostBound]; gcongr)

/-- The actual key producer has this cost and all-prefix bound on the same
trace. The input matrix is produced by the real signed-row/shift relation. -/
theorem key_run_space (regs : Fin 8 → Bool) (W bits : List Bool)
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {n B D L : ℕ} {js : List ℕ} {raw : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hn : js.length ≤ n) (hW : W.length ≤ L) (hbits : bits.length=js.length) :
    ∃ steps out,steps ≤ keyCostBound n D B L+1 ∧
      Trace AttainedSignatureProgram.program steps
        ((AttainedSignatureProgram.state regs W bits ys []).withPC
          (some AttainedSignatureProgram.program.entry))
        ((AttainedSignatureProgram.state out W bits ys
          (BucketProgram.signatureValue W bits ys)).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ steps →
        Trace AttainedSignatureProgram.program prefixSteps
          ((AttainedSignatureProgram.state regs W bits ys []).withPC
            (some AttainedSignatureProgram.program.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length ≤ keySpaceBound n D B L := by
  have hwidth : ∀ row ∈ ys,row.length=bits.length := by
    rw [hbits]
    exact BucketProgram.shiftedMatrix_rowWidth hy js.length
      (LayoutMatrixProgram.matrixRel_dimensions hr).2
  obtain ⟨steps,hsteps,out,htrace⟩ := AttainedSignatureProgram.program_runs regs W bits ys hwidth
  have hc := key_cost_le W bits hr hy hn hW hbits
  have hm := matrix_length_le W hr hy hn hW
  have hb : bits.length ≤ n := hbits ▸ hn
  refine ⟨steps,out,by omega,htrace,?_⟩
  intro prefixSteps intermediate hp ht i
  have h := AttainedSignatureProgram.prefix_stack_bound AttainedSignatureProgram.program
    regs W bits ys (hp.trans hsteps) ht i
  unfold keySpaceBound
  omega

/-- The same physical matrix envelope specialized to the actual native input. -/
def matrixEnvelope (s : LeafHeadSetupProgram.Native.Inputs) (L : ℕ) : ℕ :=
  matrixBound s.n s.D s.columnLength L

def keyEnvelope (s : LeafHeadSetupProgram.Native.Inputs) (L : ℕ) : ℕ :=
  let R := matrixEnvelope s L
  16*(L+s.n+R)+7*R+
    s.D*(BucketProgram.signatureRowBound (List.replicate L false) s.n R+2)+9

/-- Bounds consumed by the paid per-head evaluator. Only the actual generated
matrix relation, actual word lengths and fixed source scalars enter. -/
theorem generated_bounds (s : LeafHeadSetupProgram.Native.Inputs) (z L : ℕ)
    (W bits : List Bool) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys)
    (hW : W.length ≤ L)
    (hbits : bits.length=(LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z).length) :
    (words (ys.map words)).length ≤ matrixEnvelope s L ∧
      (∀ row ∈ ys,∀ x ∈ row,x.length ≤ matrixEnvelope s L) ∧
      16*(W.length+bits.length+(words (ys.map words)).length)+
        AttainedSignatureProgram.cost W bits ys+1 ≤ keyEnvelope s L := by
  have hn := LeafHeadSetupProgram.Bounds.selectedHeads_length s.n s.rows s.low z
  have hm := matrix_length_le W hr hy hn hW
  have hc := key_cost_le W bits hr hy hn hW hbits
  have hb : bits.length ≤ s.n := hbits ▸ hn
  refine ⟨hm,coefficient_bound W hr hy hn hW,?_⟩
  dsimp only [keyEnvelope,matrixEnvelope]
  dsimp only [keyCostBound] at hc
  omega

theorem matrixBound_le_monomial {n D B L U : ℕ}
    (hU : 1 ≤ U) (hn : n ≤ U) (hD : D ≤ U) (hB : B ≤ U) (hL : L ≤ U) :
    matrixBound n D B L ≤ 31*U^3 := by
  have h12 : 1 ≤ U^2 := by simpa using (Nat.pow_le_pow_left hU 2)
  have h2 : U ≤ U^2 := Nat.le_self_pow (by decide) U
  calc
    _ ≤ U*(12*U*(U+U)+6*U+1) := by unfold matrixBound; gcongr
    _ ≤ U*(31*U^2) := by gcongr; nlinarith
    _ = 31*U^3 := by ring

theorem keySpaceBound_le_monomial {n D B L U : ℕ}
    (hU : 1 ≤ U) (hn : n ≤ U) (hD : D ≤ U) (hB : B ≤ U) (hL : L ≤ U) :
    keySpaceBound n D B L ≤ 1000000*U^10 := by
  let R := matrixBound n D B L
  let W := List.replicate L false
  have hR : R ≤ 31*U^3 := matrixBound_le_monomial hU hn hD hB hL
  have hp (k : ℕ) : 1 ≤ U^k := by simpa using (Nat.pow_le_pow_left hU k)
  have h13 : U ≤ U^3 := Nat.le_self_pow (by decide) U
  have h19 : U ≤ U^9 := Nat.le_self_pow (by decide) U
  have h49 : U^4 ≤ U^9 := Nat.pow_le_pow_right hU (by decide)
  have h310 : U^3 ≤ U^10 := Nat.pow_le_pow_right hU (by decide)
  have h110 : U ≤ U^10 := Nat.le_self_pow (by decide) U
  have hw : BucketProgram.widthBound W n R ≤ 34*U^4 := by
    calc
      _ = 1+n*(L+1+R) := by simp [W,BucketProgram.widthBound]
      _ ≤ 1+U*(U+1+31*U^3) := by gcongr
      _ ≤ 1+U*(33*U^3) := by gcongr; have := hp 3; omega
      _ = 1+33*U^4 := by ring
      _ ≤ 34*U^4 := by have := hp 4; omega
  have hrow : BucketProgram.rowCostBound W n R ≤ 519000*U^9 := by
    calc
      _ ≤ (2*U)*(200*(36*U^4)^2+34)+9*(34*U^4)+22 := by
        unfold BucketProgram.rowCostBound
        gcongr <;> have := hp 4 <;> omega
      _ = 518400*U^9+68*U+306*U^4+22 := by ring
      _ ≤ 519000*U^9 := by have := hp 9; omega
  have hfirst : 9*(n*(2*R+1)) ≤ 567*U^4 := by
    calc
      _ ≤ 9*(U*(63*U^3)) := by gcongr; have := hp 3; omega
      _ = 567*U^4 := by ring
  have hsig : BucketProgram.signatureRowBound W n R ≤ 520000*U^9 := by
    unfold BucketProgram.signatureRowBound
    have := hp 9
    omega
  have hprod : D*(BucketProgram.signatureRowBound W n R+2) ≤ 520002*U^10 := by
    calc
      _ ≤ U*(520002*U^9) := by gcongr; have := hp 9; omega
      _ = 520002*U^10 := by ring
  change 16*(L+n+R)+(7*R+D*(BucketProgram.signatureRowBound W n R+2)+8)+1 ≤ _
  have := hp 10
  omega

theorem matrixEnvelope_le_monomial (s : LeafHeadSetupProgram.Native.Inputs) {L U : ℕ}
    (hU : 1 ≤ U) (hn : s.n ≤ U) (hD : s.D ≤ U) (hB : s.columnLength ≤ U) (hL : L ≤ U) :
    matrixEnvelope s L ≤ 31*U^3 :=
  matrixBound_le_monomial hU hn hD hB hL

theorem keyEnvelope_le_monomial (s : LeafHeadSetupProgram.Native.Inputs) {L U : ℕ}
    (hU : 1 ≤ U) (hn : s.n ≤ U) (hD : s.D ≤ U) (hB : s.columnLength ≤ U) (hL : L ≤ U) :
    keyEnvelope s L ≤ 1000000*U^10 := by
  have h := keySpaceBound_le_monomial hU hn hD hB hL
  dsimp only [keyEnvelope,matrixEnvelope,keySpaceBound,keyCostBound] at h ⊢
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
