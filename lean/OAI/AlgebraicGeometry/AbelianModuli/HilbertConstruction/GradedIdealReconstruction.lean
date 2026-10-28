import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreewiseRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IdealIncidence

/-! # Graded Ideal Reconstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedIdealReconstruction

noncomputable section

/-!
Actual reconstruction of a homogeneous ideal from degree submodules satisfying
the variable-multiplication incidences. Every prescribed degree is recovered,
and extracting degree relations from homogeneous ideals gives the inverse.
-/

universe u v

variable (R : Type u) [CommRing R] (σ : Type v)
attribute [local instance] MvPolynomial.gradedAlgebra

structure GradedIdealRelations where
  piece : ∀ d, Submodule R (MvPolynomial.homogeneousSubmodule σ R d)
  variable_mul : ∀ d i, piece d ≤ (piece (d + 1)).comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)

variable {R σ}

namespace GradedIdealRelations

theorem ext {D E : GradedIdealRelations R σ} (h : D.piece = E.piece) : D = E := by
  cases D
  cases E
  cases h
  rfl

variable (D : GradedIdealRelations R σ)

def toIdeal : Ideal (MvPolynomial σ R) where
  carrier := DegreewiseRelations.degreewiseRelationsSubmodule D.piece
  zero_mem' := (DegreewiseRelations.degreewiseRelationsSubmodule D.piece).zero_mem
  add_mem' := (DegreewiseRelations.degreewiseRelationsSubmodule D.piece).add_mem
  smul_mem' q _p hp := DegreewiseRelations.degreewiseRelations_mul D.piece D.variable_mul hp q

def toHomogeneousIdeal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R) :=
  ⟨D.toIdeal, by
    intro d p hp
    rw [Homogeneous.ComponentMultiplication.homogeneous_decompose_eq_component]
    exact DegreewiseRelations.degreewiseRelations_component D.piece hp d⟩

theorem toHomogeneousIdeal_degree (d : ℕ) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations D.toHomogeneousIdeal d = D.piece d := by
  apply Submodule.ext
  intro p
  exact DegreewiseRelations.degreewiseRelations_mem_homogeneous D.piece p

end GradedIdealRelations

def homogeneousIdealRelations (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    GradedIdealRelations R σ where
  piece := Homogeneous.IdealIncidence.homogeneousDegreeRelations I
  variable_mul := Homogeneous.IdealIncidence.homogeneousDegreeRelations_multiply I

theorem homogeneousIdealRelations_reconstruct
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    (homogeneousIdealRelations I).toHomogeneousIdeal = I := by
  apply HomogeneousIdeal.ext
  apply Ideal.ext
  intro p
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem I.isHomogeneous p).symm

def homogeneousIdealRelationsEquiv :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R) ≃ GradedIdealRelations R σ where
  toFun := homogeneousIdealRelations
  invFun := GradedIdealRelations.toHomogeneousIdeal
  left_inv := homogeneousIdealRelations_reconstruct
  right_inv D := by
    apply GradedIdealRelations.ext
    funext d
    exact D.toHomogeneousIdeal_degree d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedIdealReconstruction
