import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus
import Mathlib.Topology.Bases
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCoordinateChanges

/-! # Projective Countability -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCountability

/-!
# Second countability of ordinary complex projective space and its algebraic loci

The quotient projection is an open quotient map. Its domain is the subtype of
nonzero vectors in the usual countable product of copies of the complex numbers,
which is second countable. The image of a countable topological basis gives a
countable basis on projective space. Subspaces inherit second countability.

In particular, this applies to every finite-dimensional coordinate projective
space and every homogeneous polynomial locus in it. No scheme analytification or
smoothness statement is assumed.
-/

variable {ι : Type*} [Countable ι]

/-- The ordinary quotient topology on complex coordinate projective space has a
countable basis whenever its coordinate index type is countable. -/
instance complexProjectivization_secondCountableTopology :
    SecondCountableTopology (Projectivization ℂ (ι → ℂ)) := by
  let : SecondCountableTopology (ι → ℂ) := inferInstance
  let : SecondCountableTopology {v : ι → ℂ // v ≠ 0} :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact Topology.IsOpenQuotientMap.secondCountableTopology
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap ProjectiveZeroLocus.isOpenMap_projectivization_mk'
      (ProjectiveCompactness.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)))

/-- Ordinary complex projective n-space is second countable. -/
theorem complexProjectiveSpace_secondCountable (n : ℕ) :
    SecondCountableTopology (Projectivization ℂ (Fin (n + 1) → ℂ)) :=
  inferInstance

/-- The projectivization of any finite-dimensional complex normed space is
second countable, by the actual homeomorphism supplied by a finite basis. -/
theorem finiteDimensionalProjectivization_secondCountableTopology
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    SecondCountableTopology (Projectivization ℂ V) :=
  (ProjectiveCoordinateChanges.projectivizationCoordinates V).isEmbedding.secondCountableTopology

/-- A genuine homogeneous polynomial zero locus has the inherited countable
basis from ordinary complex projective space. -/
theorem homogeneousProjectiveZeroLocus_secondCountableTopology
    (f : MvPolynomial ι ℂ) {d : ℕ} (hf : f.IsHomogeneous d) :
    SecondCountableTopology (Foundations.Scheme.ProjectiveZeroLocus.homogeneousProjectiveZeroLocus f hf) :=
  inferInstance

/-- The common zero locus of any family of homogeneous equations is second
countable, without requiring that the family of equations itself be countable. -/
theorem projectiveCommonZeroLocus_secondCountableTopology {κ : Type*}
    (f : κ → MvPolynomial ι ℂ) (d : κ → ℕ)
    (hf : ∀ k, (f k).IsHomogeneous (d k)) :
    SecondCountableTopology (Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus f d hf) :=
  inferInstance

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCountability
