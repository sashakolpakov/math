import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.QuotientFinitePresentation
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Degree Rank Specialization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.DegreeRankSpecialization.GradedHilbert

noncomputable section

/-! A flat homogeneous degree quotient over a local ring is finite free, so its
rank equals the dimension of the actual quotient after field specialization. -/

open _root_.MvPolynomial TensorProduct

universe u v z
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K]
variable {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneousDegree_finrank_baseChange_of_local_flat
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N))] :
    Module.finrank K (Hilbert.Polynomial.GradedHilbert.DegreeQuotient
      (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R K) g) N
        (fun i => (hg i).map (algebraMap R K))).toIdeal (d + N)) =
      Module.finrank R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) := by
  let := Homogeneous.QuotientFinitePresentation.GradedHilbert.homogeneousGeneratorsDegree_finitePresentation g N hg d
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) :=
    Module.free_of_flat_of_isLocalRing
  rw [← (Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsDegreeBaseChangeEquiv (S := K) g N hg (d + N)).finrank_eq]
  exact Module.finrank_baseChange

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.DegreeRankSpecialization.GradedHilbert
