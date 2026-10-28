import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexTateCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsFrameLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexBasis

/-! # Complex Block Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexBlockBasis.Construction

noncomputable section

/-!
The original complex PEL family has integral Tate blocks of rank three.
The basis is constructed from its actual period module and action, with
no additional block-rank or frame hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexBasis

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  {N : ℕ} (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation F.abelian.scheme.left F.abelian.scheme.hom)

def complexCMPointsBlockBasis (τ : Gal(E/ℚ)) :
    Module.Basis (Fin 3) ℤ_[q]
      (CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F τ) := by
  have := TateComparison.ComplexBasis.complexIntegralTateImage_isLattice F.abelian P q
  exact CM.PointsFrameLattice.Construction.l45TateBlockBasisOfFrame j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F
    (ComplexTateCoordinates.Construction.complexTateEmbeddingCoordinates j iota hsplit s hs hdegree F.abelian P (TateComparison.PELAdapters.actionFromEnd F.action))
    (fun a x i υ => by
      have h := ComplexTateCoordinates.Construction.complexTateEmbeddingCoordinates_action j iota hsplit s hs hdegree
        F.abelian P (TateComparison.PELAdapters.actionFromEnd F.action) a x i υ
      rw [RationalSplitCompletion.Construction.l45FieldCharacter_integer] at h
      exact h) τ

include P hs hdegree in
theorem complexCMPointsBlock_finrank (τ : Gal(E/ℚ)) :
    Module.finrank ℤ_[q]
      (CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F τ) = 3 := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (complexCMPointsBlockBasis j iota hsplit s hs hdegree F P τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexBlockBasis.Construction
