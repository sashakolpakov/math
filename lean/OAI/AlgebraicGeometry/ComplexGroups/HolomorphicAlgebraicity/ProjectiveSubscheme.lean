import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveComplexPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus
import OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed

/-! # Projective Subscheme -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme.Constructions.Algebraization

noncomputable section

/-!
# Reduced projective schemes for homogeneous equations

The homogeneous zero locus in the actual `Proj` scheme carries its reduced
induced scheme structure. Its complex-valued points are exactly the ordinary
projective common zero locus, by the proved field-point lifting theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem exists_reduced_projective_subscheme_of_equations
    {n : ℕ} {κ : Type*} (f : κ → MvPolynomial (Fin (n + 1)) ℂ)
    (degree : κ → ℕ) (hf : ∀ k, (f k).IsHomogeneous (degree k)) :
    ∃ (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)),
      IsReduced X.left ∧ IsClosedImmersion i.left ∧ IsProper X.hom ∧
      ∀ p : Projectivization ℂ (Fin (n + 1) → ℂ),
        Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n p ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔
          p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus f degree hf := by
  let Z : TopologicalSpace.Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
    ⟨ProjectiveSpectrum.zeroLocus (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (range f),
      ProjectiveSpectrum.isClosed_zeroLocus _ _⟩
  let X := Over.mk (CycleClass.Geometric.ReducedClosed.reducedClosedι Z ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let i : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Over.homMk (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) rfl
  have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (CycleClass.Geometric.ReducedClosed.reducedClosedι Z))
  have hX : IsReduced X.left := inferInstanceAs (IsReduced (CycleClass.Geometric.ReducedClosed.reducedClosedScheme Z))
  have hp : IsProper X.hom := by
    change IsProper (CycleClass.Geometric.ReducedClosed.reducedClosedι Z ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    infer_instance
  refine ⟨X, i, hX, hi, hp, ?_⟩
  intro p
  change Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n p ∈ range (fun q => q ≫ i) ↔ _
  rw [Foundations.Scheme.ImmersionComplexPoints.range_closedImmersion_complexPointMap i]
  change Foundations.Scheme.ProjectiveVectorScale.projectivizationPoint n p (⊥ : PrimeSpectrum ℂ) ∈ range (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) ↔ _
  rw [CycleClass.Geometric.ReducedClosed.range_reducedClosedι]
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
    change Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv (⊥ : PrimeSpectrum ℂ) ∈
      ProjectiveSpectrum.zeroLocus (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (range f) ↔ _
    change (range f ⊆ (Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv (⊥ : PrimeSpectrum ℂ)).asHomogeneousIdeal) ↔ _
    rw [range_subset_iff]
    exact forall_congr' fun k => Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff
      v hv (f k) (degree k) (hf k) _

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme.Constructions.Algebraization
