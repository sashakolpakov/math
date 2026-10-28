import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramSourceFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramFamily
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramBlockCode

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

noncomputable def packedSourceValue {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D) (i : ℕ) :
    Polynomial (p.model.O p.t) :=
  if hi : i < D then packedValue P p.rows row ⟨i,hi⟩ else 0

theorem packedSourceValue_degree {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D) (i : ℕ) :
    (packedSourceValue p P row i).natDegree ≤ p.R := by
  unfold packedSourceValue
  split_ifs with hi
  · unfold packedValue
    split
    · split_ifs <;> simp
    · split
      · simp
      · split_ifs
        · exact LayoutScaledMatrices.sourceRow_degree _ _ _ _ _ _ _
        · simp
  · simp

noncomputable def totalPackedSource {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : ℕ) :
    Polynomial (p.model.O p.t) :=
  if hr : row < D then packedSourceValue p P ⟨row,hr⟩ col else 0

theorem totalPackedSource_degree {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : ℕ) :
    (totalPackedSource p P row col).natDegree ≤ p.R := by
  unfold totalPackedSource
  split_ifs
  · exact packedSourceValue_degree p P _ col
  · simp

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
