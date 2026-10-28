import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.SingleDegreeGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ProjectiveFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatness

/-! # Finite Persistence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-!
A bound depending only on the number of variables and the generating degree
makes the finite generation conditions sufficient for flatness in every degree.
This uses the constructive uniform syzygy bound, without assuming persistence.
-/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatness.GradedHilbert

universe u

def FinitePersistence.truncatedFlatnessBound (n N : ℕ) : ℕ :=
  N + HilbertScheme.Presentations.Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) N

variable {R : Type u} [CommRing R] {n B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r) (N : ℕ)

theorem GradedClassification.TruncatedGradedQuotientData.degreeQuotient_flat_of_generatedFromDegree
    (hB : FinitePersistence.truncatedFlatnessBound n N ≤ B) (hgen : D.GeneratedFromDegree N) (d : ℕ) :
    Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient D.generatedIdeal.toIdeal d) := by
  have hN : N ≤ B := (Nat.le_add_right N _).trans hB
  by_cases hd : d < N
  · have := D.retainedDegreeQuotient_projective ⟨d, by omega⟩
    exact Module.Flat.of_projective
  let g : Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n :=
    fun i => (D.degreeGenerators ⟨N, Nat.lt_succ_of_le hN⟩ i).val
  have hg : ∀ i, (g i).IsHomogeneous N := fun i =>
    (D.degreeGenerators ⟨N, Nat.lt_succ_of_le hN⟩ i).property
  have hI : D.generatedIdeal = HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg :=
    HomogeneousIdeal.ext (D.generatedIdeal_span_generators N hN hgen)
  have hflat : ∀ e ≤ HilbertScheme.Presentations.Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n
      (Fintype.card (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) N,
      Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N)) := by
    intro e he
    rw [← hI]
    have hb : e + N < B + 1 := by
      change N + HilbertScheme.Presentations.Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n
        (Fintype.card (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) N ≤ B at hB
      omega
    have := D.retainedDegreeQuotient_projective ⟨e + N, hb⟩
    exact Module.Flat.of_projective
  rw [hI, ← Nat.sub_add_cancel (show N ≤ d by omega)]
  exact HilbertScheme.Presentations.Finite.DegreeFlatness.GradedHilbert.homogeneous_quotients_flat_of_finite_flat_degrees g N hg hflat (d - N)

theorem GradedClassification.TruncatedGradedQuotientData.projectiveFamily_flat_of_generatedFromDegree
    (hB : FinitePersistence.truncatedFlatnessBound n N ≤ B) (hgen : D.GeneratedFromDegree N) :
    Flat D.projectiveFamily.hom :=
  D.projectiveFamily_flat 0 (fun d _ => D.degreeQuotient_flat_of_generatedFromDegree N hB hgen d)

def GradedClassification.TruncatedGradedQuotientData.generatedFlatClosedFamily
    (hB : FinitePersistence.truncatedFlatnessBound n N ≤ B) (hgen : D.GeneratedFromDegree N) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  D.flatClosedFamily 0 (fun d _ => D.degreeQuotient_flat_of_generatedFromDegree N hB hgen d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
