import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Determinants
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Ideal.Grassmannian

noncomputable section

/-!
The homogeneous ideal of universal Plücker relations. An auxiliary
degree-one variable records the common scale of the maximal minors, so the
construction treats rank zero and positive rank uniformly.
-/

open _root_.MvPolynomial

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

def genericQuotientMatrix : Matrix ι ν (MvPolynomial (ι × ν) R) := fun i j => X (i, j)

def pluckerMinorPolynomial (a : ι → ν) : MvPolynomial (ι × ν) R :=
  Determinants.Grassmannian.maximalMinor (genericQuotientMatrix (R := R)) a

def pluckerEvaluation : MvPolynomial (ι → ν) R →+* MvPolynomial Unit (MvPolynomial (ι × ν) R) :=
  eval₂Hom (C.comp C) (fun a => C (pluckerMinorPolynomial (R := R) a) * X ())

instance pluckerCoordinateGradedAlgebra :
    GradedAlgebra (homogeneousSubmodule (ι → ν) R) := MvPolynomial.gradedAlgebra

instance pluckerScaledMatrixGradedAlgebra :
    GradedAlgebra (homogeneousSubmodule Unit (MvPolynomial (ι × ν) R)) := MvPolynomial.gradedAlgebra

def gradedPluckerEvaluation : homogeneousSubmodule (ι → ν) R →+*ᵍ
    homogeneousSubmodule Unit (MvPolynomial (ι × ν) R) where
  __ := pluckerEvaluation (R := R) (ι := ι) (ν := ν)
  map_mem {d} {p} hp := by
    change (eval₂ (C.comp C)
      (fun a : ι → ν => C (pluckerMinorPolynomial (R := R) a) * X ()) p).IsHomogeneous d
    have h := hp.eval₂ (C.comp C)
      (fun a => C (pluckerMinorPolynomial (R := R) a) * X ())
      (fun r => isHomogeneous_C Unit (C r))
      (fun a => (isHomogeneous_X _ ()).C_mul (pluckerMinorPolynomial (R := R) a))
    simpa only [one_mul] using h

def pluckerIdeal : HomogeneousIdeal (homogeneousSubmodule (ι → ν) R) :=
  (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit (MvPolynomial (ι × ν) R))).comap
    gradedPluckerEvaluation

theorem mem_pluckerIdeal (p : MvPolynomial (ι → ν) R) :
    p ∈ pluckerIdeal (R := R) (ι := ι) (ν := ν) ↔
      pluckerEvaluation (R := R) (ι := ι) (ν := ν) p = 0 := Iff.rfl

@[simp] theorem pluckerEvaluation_X (a : ι → ν) :
    pluckerEvaluation (R := R) (ι := ι) (ν := ν) (X a) =
      C (pluckerMinorPolynomial (R := R) a) * X () := by
  exact eval₂_X (C.comp C)
    (fun b : ι → ν => C (pluckerMinorPolynomial (R := R) b) * X ()) a

/-- Evaluation of the universal matrix minors at an actual quotient matrix. -/
theorem eval_pluckerMinorPolynomial (Q : Matrix ι ν R) (a : ι → ν) :
    eval (fun p : ι × ν => Q p.1 p.2) (pluckerMinorPolynomial a) = Determinants.Grassmannian.maximalMinor Q a := by
  change (eval (fun p : ι × ν => Q p.1 p.2))
    (Determinants.Grassmannian.maximalMinor (genericQuotientMatrix (R := R)) a) = _
  rw [← Determinants.Grassmannian.maximalMinor_map]
  congr 1
  ext i j
  exact eval_X (i, j)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Ideal.Grassmannian
