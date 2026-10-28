import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.TupleRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.HomPackageAssembly
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.RepresentationProjectiveReduction

/-! # Tuple Package Assembly -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.TuplePackageAssembly.Core

noncomputable section

/-! Assemble all finite Hilbert/Hom tuple data from the individual
exact Hilbert representations, including projectivity and the graph open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] (X Y : Over S)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]
variable (B : Has.Core.ProjectivePresentation (X ⨯ Y)) (n : ℕ) (P : Fin n → Polynomial ℚ)

theorem hilbertHomLoci_of_component_representations
    (H : Fin n → Over S) (BH : ∀ i, Has.Core.ProjectivePresentation (H i))
    (eH : ∀ i, yoneda.obj (H i) ≅ (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B (P i)).toFunctor) :
    Nonempty (Loci.Core.HilbertHomLoci X Y B n P) := by
  let e : yoneda.obj (Finite.ParameterProducts.Core.finiteParameterProduct n H) ≅
      (Presentations.Polynomial.TupleSubfunctors.Core.hilbertPolynomialTupleSubfunctor X Y n B P).toFunctor :=
    Finite.TupleRepresentation.Core.finiteTupleRepresentation (fun i => PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B (P i)) H eH
  exact HomPackageAssembly.Core.hilbertHomLoci_of_projective_hilbert X Y B n P (Finite.ParameterProducts.Core.finiteParameterProduct n H)
    (Finite.ParameterProducts.Core.finiteParameterProjectivePresentation H BH) e

theorem hilbertHomLoci_of_projective_space_components
    (H : Fin n → Over S) (BH : ∀ i, Has.Core.ProjectivePresentation (H i))
    (eH : ∀ i, yoneda.obj (H i) ≅
      (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S B.dimension) (P i)).toFunctor) :
    Nonempty (Loci.Core.HilbertHomLoci X Y B n P) := by
  have h (i : Fin n) : ∃ Z : Over S, Has.Core.IsProjectiveOver Z ∧
      Nonempty (yoneda.obj Z ≅ (PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor B (P i)).toFunctor) :=
    RepresentationProjectiveReduction.Core.hilbert_representation_of_projective_space B (P i) (H i) (BH i) (eH i)
  choose Z hZ eZ using h
  exact hilbertHomLoci_of_component_representations X Y B n P Z
    (fun i => Classical.choice (hZ i)) (fun i => Classical.choice (eZ i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.TuplePackageAssembly.Core
