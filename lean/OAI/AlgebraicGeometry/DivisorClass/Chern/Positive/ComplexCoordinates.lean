import OAI.AlgebraicGeometry.DivisorClass.Chern.OrderedRadialNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.OrthantGenerator

/-! # Complex Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.ComplexCoordinates

noncomputable section

/-! The original ordered complex coordinates in the positive-dimensional
degree convention used by the explicit Euclidean fillings. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def positiveComplexRealCoordinates (p : ℕ) :
    (Fin (p + 1) → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * p + 2)) := by
  simpa only [Nat.mul_succ] using CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv (p + 1)

def positiveComplexRealPuncturedCoordinates (p : ℕ) :
    CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ) ≃ₜ
      CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2))) :=
  CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (positiveComplexRealCoordinates p)

def positiveEuclideanToComplex (p : ℕ) :
    TopCat.of (EuclideanSpace ℝ (Fin (2 * p + 2))) ⟶ TopCat.of (Fin (p + 1) → ℂ) :=
  TopCat.ofHom ⟨(positiveComplexRealCoordinates p).symm,
    (positiveComplexRealCoordinates p).symm.continuous⟩

def positiveEuclideanToComplexPunctured (p : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2)))) ⟶
      TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (Fin (p + 1) → ℂ)) :=
  TopCat.ofHom ⟨(positiveComplexRealPuncturedCoordinates p).symm,
    (positiveComplexRealPuncturedCoordinates p).symm.continuous⟩

theorem positiveEuclideanToComplex_inclusion (p : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ) ≫
        positiveEuclideanToComplex p =
      positiveEuclideanToComplexPunctured p ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) := rfl

theorem positiveEuclideanToComplexPunctured_coordinates (p : ℕ) :
    positiveEuclideanToComplexPunctured p ≫
      TopCat.ofHom ⟨positiveComplexRealPuncturedCoordinates p,
        (positiveComplexRealPuncturedCoordinates p).continuous⟩ =
      𝟙 (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p + 2))))) := by
  apply TopCat.ext
  intro x
  exact (positiveComplexRealPuncturedCoordinates p).apply_symm_apply x

theorem positiveComplexNormalLocalStandardSphereIso_ordered (p n : ℕ) (hn : n ≠ 0) :
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p n hn).hom =
      CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) n ≫
        CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom ⟨positiveComplexRealPuncturedCoordinates p,
            (positiveComplexRealPuncturedCoordinates p).continuous⟩) n ≫
        CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 2))))) n := by
  simpa only [CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso, positiveComplexRealPuncturedCoordinates,
    positiveComplexRealCoordinates, CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph, Nat.mul_succ, id_eq,
    CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereHomology, CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere] using
      OrderedRadialNaturality.complexNormalLocalRealSphereIso_ordered (p + 1) n hn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.ComplexCoordinates
