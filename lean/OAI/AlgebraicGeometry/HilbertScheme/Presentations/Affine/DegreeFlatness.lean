import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.StalkFlatness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange

/-! # Degree Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.DegreeFlatness.GradedHilbert

noncomputable section

/-! Flatness of homogeneous coordinate quotients over an affine parameter
scheme is detected by the actual coefficient-specialized quotients in its stalks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial TensorProduct

universe u

theorem affine_homogeneous_quotient_flat (X : Scheme.{u}) [IsAffine X] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(X, ⊤) n)) (d : ℕ)
    (h : ∀ x : X,
      letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.Γgerm x).hom.toAlgebra
      Module.Flat (X.presheaf.stalk x)
        (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := X.presheaf.stalk x) I).toIdeal d)) :
    Module.Flat Γ(X, ⊤) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  apply StalkFlatness.affineModule_flat_of_stalk_tensor X
  intro x
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.Γgerm x).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk x)
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := X.presheaf.stalk x) I).toIdeal d) := h x
  exact Module.Flat.of_linearEquiv (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := X.presheaf.stalk x) I d)

theorem affine_generated_quotient_flat (X : Scheme.{u}) [IsAffine X] {n : ℕ} {ι : Type u}
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing Γ(X, ⊤) n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    (h : ∀ x : X, Module.Flat (X.presheaf.stalk x)
      (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (X.presheaf.Γgerm x).hom g) N
        (fun i => (hg i).map _)).toIdeal d)) :
    Module.Flat Γ(X, ⊤) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal d) := by
  apply affine_homogeneous_quotient_flat X
  intro x
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) := (X.presheaf.Γgerm x).hom.toAlgebra
  rw [Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsIdeal_baseChange]
  exact h x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.DegreeFlatness.GradedHilbert
