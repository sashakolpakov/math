import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReconstructedClosedFamilies
import Mathlib.RingTheory.Grassmannian

/-! # Graded Quotient Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedQuotientFamilies

noncomputable section

/-!
Compatible fixed-rank Grassmannian quotients in all degrees reconstruct an
actual homogeneous ideal and a proper flat projective family. Over noetherian
coefficient rings this is an HilbertConstruction flat finitely presented closed family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (R : Type u) [CommRing R] (σ : Type v) (r : ℕ → ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

structure GradedQuotientData where
  quotient : ∀ d, Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) (r d)
  variable_mul : ∀ d i, (quotient d).toSubmodule ≤
    ((quotient (d + 1)).toSubmodule).comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)

variable {R σ r}

namespace GradedQuotientData

variable (D : GradedQuotientData R σ r)

def relations : GradedIdealReconstruction.GradedIdealRelations R σ where
  piece d := (D.quotient d).toSubmodule
  variable_mul := D.variable_mul

def ideal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R) :=
  D.relations.toHomogeneousIdeal

theorem degreeRelations_eq (d : ℕ) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations D.ideal d = (D.quotient d).toSubmodule :=
  D.relations.toHomogeneousIdeal_degree d

theorem degree_flat (d : ℕ) :
    Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ D.relations.piece d) := by
  change Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ (D.quotient d).toSubmodule)
  infer_instance

theorem quotient_flat : Module.Flat R (MvPolynomial σ R ⧸ D.ideal.toIdeal) :=
  D.relations.quotient_flat_iff.mpr D.degree_flat

theorem degree_rank (d : ℕ) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (MvPolynomial.homogeneousSubmodule σ R d ⧸ Homogeneous.IdealIncidence.homogeneousDegreeRelations D.ideal d) p = r d := by
  rw [D.degreeRelations_eq]
  exact (D.quotient d).rankAtStalk_eq p

end GradedQuotientData

variable {τ : Type u} [Finite τ] (D : GradedQuotientData R τ r)

omit [Finite τ] in
theorem GradedQuotientData.projectiveFamily_flat : Flat D.relations.projectiveFamily.hom :=
  D.relations.projectiveFamily_flat D.degree_flat

def GradedQuotientData.flatClosedFamily [IsNoetherianRing R] : Closed.Families.FlatClosedFamily
    (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (MvPolynomial.homogeneousSubmodule τ R))) :=
  D.relations.flatClosedFamily D.degree_flat

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedQuotientFamilies
