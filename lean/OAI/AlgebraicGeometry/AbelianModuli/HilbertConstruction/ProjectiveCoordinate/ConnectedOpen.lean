import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedFieldCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelAffineFieldTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ConnectednessFieldTests

/-! # Connected Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedOpen

noncomputable section

/-! A pointed proper smooth projective coordinate quotient over a Noetherian ring has an actual open subset classifying exactly its geometrically connected base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem pointedProperSmoothProjectiveCoordinate_connected_open
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _) :
    ∃ U : (Spec (.of R)).Opens, ∀ (T : Scheme.{u}) (c : T ⟶ Spec (.of R)),
      GeometricallyConnected (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) c) ↔
        Set.range c ⊆ (U : Set (Spec (.of R))) := by
  obtain ⟨m, k, B, hB⟩ := Projective.GlobalFunctionsMatrix.flatProjectiveCoordinate_globalFunctions_uniform_matrix I
  let U := Matrix.KernelDimensionOpen.matrixKernelDimensionOpen (B.map (Scheme.ΓSpecIso (.of R)).inv.hom) 1
  have hf : ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ Spec (.of R)),
      GeometricallyConnected (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) c) ↔
        Set.range c ⊆ (U : Set (Spec (.of R))) := by
    intro K _ c
    let φ : R →+* K := (Spec.fullyFaithful.preimage c).unop.hom
    have hc : Spec.map (CommRingCat.ofHom φ) = c := Spec.fullyFaithful.map_preimage c
    have ht : GeometricallyConnected (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
        (Spec.map (CommRingCat.ofHom φ))) ↔
        Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆ (U : Set (Spec (.of R))) := by
      let := φ.toAlgebra
      exact (ConnectedFieldCriterion.projectiveCoordinate_connected_field_kernel I x hx B (Classical.choice (hB K))).trans
        (Matrix.KernelAffineFieldTests.matrixKernelDimensionOpen_specMap φ B 1).symm
    exact hc ▸ ht
  exact ⟨U, fun _ c => Geometric.ConnectednessFieldTests.geometricallyConnected_open_field_tests
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) U hf c⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedOpen
