import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.EmbeddedTorsionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationRetraction

/-! # Even Graph Evaluation Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The high-torsion evaluation map has an actual linear retraction
on a complete framed affine chart. This is the splitting needed for
the cokernel flatness of polynomial evaluation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {R : Type u} [CommRing R] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.completeFramedEvenGraphEvaluation_leftInverse
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t) (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (B : A.CompleteFramedEvenGraphSections level t) :
    ∃ q : (Multiplicative (Fin (2 * g) → ZMod n) → R) →ₗ[R]
        (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower (2 * t)).sheaf,
      q.comp (A.fullLevelAffineEvenGraphEvaluation level t B.frames) = LinearMap.id := by
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
    (A.graphBundle.tensorPower (2 * t)).sheaf B.basis
  obtain ⟨Q, hQ⟩ := A.evenGraphFamilyEvaluationMatrix_leftInverse hg hδ hN hunit
    level t ht htlarge hlarge s B.geometricComplete B.frames
  have heq : Affine.GeometricMatrixSplitting.affineCoordinateMatrix (A.evenGraphFamilyEvaluationMatrix level t s B.frames) =
      BasisEvaluationMatrices.basisEvaluationMatrix B.basis (A.fullLevelAffineEvenGraphEvaluation level t B.frames) := rfl
  rw [heq] at hQ
  exact BasisEvaluationRetraction.linearEvaluation_leftInverse_of_basisMatrix B.basis _ Q hQ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
