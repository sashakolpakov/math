import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Loci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TupleSubfunctors

/-! # Hom Exact Subfunctors -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! The subfunctors appearing in a Hilbert/Hom representation package
are the canonical polynomial subfunctors, by their exact membership predicates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]
variable {B : Has.Core.ProjectivePresentation (X ⨯ Y)} {n : ℕ} {P : Fin n → Polynomial ℚ}

theorem Loci.Core.HilbertHomLoci.hilbertLocus_eq (L : Loci.Core.HilbertHomLoci X Y B n P) :
    L.hilbertLocus = Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P := by
  ext T I
  exact L.hilbert_mem T.unop I

theorem Loci.Core.HilbertHomLoci.morphismLocus_eq (L : Loci.Core.HilbertHomLoci X Y B n P) :
    L.morphismLocus = Presentations.Polynomial.TupleSubfunctors.Core.morphismPolynomialTupleSubfunctor X Y n B P := by
  ext T f
  exact L.morphism_mem T.unop f

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
