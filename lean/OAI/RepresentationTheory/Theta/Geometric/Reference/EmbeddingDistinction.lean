import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexCoordinates

/-! # Embedding Distinction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.EmbeddingDistinction

noncomputable section

/-! The complete original CM-type enumeration distinguishes every
chosen embedding from the others and from all conjugate choices. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexCoordinates

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem reference_embedding_injective : Function.Injective P.embeddings := by
  intro i j h
  have he : (i, false) = (j, false) := hP.1.1 (by simpa only [Bool.false_eq_true, ite_false] using h)
  exact congrArg Prod.fst he

include hP in
theorem reference_conjugate_embedding_ne (i j : Fin s) :
    AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i) ≠ P.embeddings j := by
  intro h
  have he : (i, true) = (j, false) := hP.1.1 (by simpa only [ite_eq_left, ite_false, Bool.false_eq_true] using h)
  exact Bool.noConfusion (congrArg Prod.snd he)

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.EmbeddingDistinction
