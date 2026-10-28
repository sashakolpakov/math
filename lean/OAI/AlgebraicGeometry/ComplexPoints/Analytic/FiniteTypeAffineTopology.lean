import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.GeneratingCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Finite Type Affine Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology

/-!
# Ordinary topology of finite-type affine complex points

A finite polynomial presentation embeds the actual complex-character space as
a closed subspace of a finite-dimensional complex coordinate space. This gives
local compactness. Finite generating coordinates also give second countability.
No smoothness assumption is needed for either property.
-/

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- A surjective polynomial presentation gives a closed embedding by its actual
coordinate functions. -/
theorem isClosedEmbedding_polynomialPresentation {ι : Type*}
    (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => fun i : ι => x (f (MvPolynomial.X i))) := by
  exact (PolynomialEvaluation.polynomialPointHomeomorph ι).isClosedEmbedding.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective f hf)

/-- A finite-type complex affine point space is a closed subspace of some
finite-dimensional complex coordinate space. -/
theorem finiteTypeAffinePoints_exists_closedEmbedding [Algebra.FiniteType ℂ A] :
    ∃ (n : ℕ) (f : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → Fin n → ℂ), Topology.IsClosedEmbedding f := by
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℂ) (S := A)).mp inferInstance
  exact ⟨n, (fun x i => x (f (MvPolynomial.X i))),
    isClosedEmbedding_polynomialPresentation f hf⟩

/-- The ordinary point topology of a finite-type complex algebra is second
countable: finite algebra generators embed it in a finite complex product. -/
instance finiteTypeAffinePoints_secondCountable [Algebra.FiniteType ℂ A] :
    SecondCountableTopology (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℂ) (A := A)
  have hg : Algebra.adjoin ℂ (Set.range (fun i : s => (i : A))) = ⊤ := by
    have hr : Set.range (fun i : s => (i : A)) = (s : Set A) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [hr]
    exact hs
  exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isInducing_coordinates (fun i : s => (i : A)) hg).secondCountableTopology

/-- Finite-type affine complex point spaces are locally compact in the ordinary
evaluation topology, including at singular points. -/
instance finiteTypeAffinePoints_locallyCompact [Algebra.FiniteType ℂ A] :
    LocallyCompactSpace (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) := by
  obtain ⟨n, f, hf⟩ := finiteTypeAffinePoints_exists_closedEmbedding (A := A)
  exact hf.locallyCompactSpace

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
