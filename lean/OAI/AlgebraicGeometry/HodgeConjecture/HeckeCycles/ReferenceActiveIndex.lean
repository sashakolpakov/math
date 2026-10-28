import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Identity

/-! # Reference Active Index -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceActiveIndex.CM.Reference

noncomputable section

/-! The zero-indexed auxiliary reference matches the active label and
all three operators of the original ordinary construction. -/

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hs : 0 < s) (hzero : D.reference.distinguished.val = 0)

include hzero

theorem index : D.reference.distinguished = (⟨0, hs⟩ : Fin s) := Fin.ext hzero

theorem character (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (hlabels : D.localCharacter = fun w => j.localCharacter D.fieldEmbedding (labels w))
    (hactive : labels (⟨0, hs⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E) :
    D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) := by
  rw [hlabels, index E D hs hzero]
  exact congrArg (j.localCharacter D.fieldEmbedding) hactive

theorem operators (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (fullSide : Fin s → Bool) :
    (fun i : Fin 3 => A.basis (Neighbor.Types.CM.integralType D.reference.distinguished fullSide i).val) =
      (fun i : Fin 3 => A.basis (Neighbor.Types.CM.integralType ⟨0, hs⟩ fullSide i).val) :=
  congrArg (fun active : Fin s => fun i : Fin 3 =>
    A.basis (Neighbor.Types.CM.integralType active fullSide i).val) (index E D hs hzero)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceActiveIndex.CM.Reference
