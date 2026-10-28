import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramSource

namespace OAI.Algorithms

/-! Adapter from the native owner-fiber loop to the matrix builder's fixed-bank
entry contract.  The incidence callback is still an actual command/Eval premise;
there is no table of precomputed entry values. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def matrixBase (base : Fin 288 → List Bool) (j : ℕ) : Data :=
  LayoutMatrixProgram.entryState base (fun _ => false) (unary j) [] [] []

theorem matrix_data (base : Fin 288 → List Bool) (j : ℕ)
    (hb : Ready (matrixBase base j)) (regs : Fin 16 → Bool)
    (col : List Bool) (result : WordPair) :
    data (matrixBase base j) regs [] col ([],[]) result =
      LayoutMatrixProgram.entryState base regs (unary j) col result.1 result.2 := by
  have h212 := hb.2 212 (by decide) (by decide)
  have h213 := hb.2 213 (by decide) (by decide)
  have h214 := hb.2 214 (by decide) (by decide)
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h : i=212
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h212.symm
    by_cases h' : i=213
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h213.symm
    by_cases h'' : i=214
    · subst i; simpa [matrixBase,LayoutMatrixProgram.entryState,data,bank] using h214.symm
    by_cases hr : i=252
    · subst i; simp [matrixBase,LayoutMatrixProgram.entryState,bank]
    by_cases hc : i=253
    · subst i; simp [bank]
    by_cases hp : i=254
    · subst i; simp [bank]
    by_cases hn : i=255
    · subst i; simp [bank]
    simp [matrixBase,LayoutMatrixProgram.entryState,bank,h,h',h'',hr,hc,hp,hn]

/-- Native original-column contract. The time and length inequalities are the
only uniform resource envelopes added to the pointwise owner-fiber theorem.
The caller may retain both the exact signed sum and the literal mass bound in
its desired relation. -/
theorem entryContract (entry : Code) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → WordPair → Prop)
    (ps : List (ℕ × ℕ)) (value : ℕ → ℕ → ℤ)
    (Ti Bi Mi Tout Bout : ℕ)
    (hready : ∀ j v, Valid j v → Ready (matrixBase base j))
    (hsource : base (LayoutMatrixProgram.bankPort 201)=LayoutOwnerFiberProgram.stream ps)
    (hentry : ∀ j v, Valid j v → ∀ i∈LayoutOwnerFiberProgram.fiberIndices v 0 ps,
      EntryAt entry (parked (matrixBase base j) v) (value j) Ti Bi Mi i)
    (htime : ∀ j v, Valid j v → budget Ti Bi ps.length v ps ≤ Tout)
    (hlength : ∀ j v, Valid j v →
      (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*(Bi+2) ≤ Bout)
    (hrel : ∀ j v, Valid j v → ∀ result : WordPair,
      pairValue result=((LayoutOwnerFiberProgram.fiberIndices v 0 ps).map (value j)).sum →
      pairTotal result.1 result.2 ≤ (LayoutOwnerFiberProgram.fiberIndices v 0 ps).length*Mi →
      Rel j v result) :
    LayoutMatrixProgram.EntryContract (command entry) base Valid Rel Tout Bout := by
  intro regs j v hv
  have hb := hready j v hv
  have hs : (matrixBase base j).stacks 201=LayoutOwnerFiberProgram.stream ps := by
    simpa [matrixBase,LayoutMatrixProgram.entryState] using hsource
  obtain ⟨n,hn,rf,result,he,heq,hlen,hmass⟩ := command_eval entry (matrixBase base j) hb
    v ps hs (value j) Ti Bi Mi ps.length (hentry j v hv)
    (by
      intro i hi
      exact Nat.le_of_lt (LayoutOwnerFiberProgram.mem_fiberIndices_lt v ps hi)) regs
  rw [matrix_data base j hb regs, matrix_data base j hb rf] at he
  refine ⟨n,le_trans (Nat.le_of_lt hn) (htime j v hv),rf,result,he,hrel j v hv result heq hmass,?_⟩
  exact le_trans hlen (hlength j v hv)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
