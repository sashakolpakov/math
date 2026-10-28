import OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexUniversalCoefficient
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Dual Complex Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality.Cycles

noncomputable section

/-!
# Naturality of dual-complex evaluation and universal coefficients

Precomposition by an actual chain map gives the actual map of linear Hom
cochain complexes. The evaluation pairing descends naturally through both
cycle quotients. Over a field, the canonical universal-coefficient equivalence
therefore intertwines cohomological pullback and precomposition on homology.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

section Evaluation

variable {R : Type} [CommRing R]
variable {C D E : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Linear Hom pullback preserves the identity chain map. -/
@[simp]
theorem linearHomCochainMap_id (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (M : ModuleCat.{0} R) :
    DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (𝟙 C) M = 𝟙 (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex C M) := by
  ext n φ
  rfl

/-- Linear Hom pullback reverses composition of actual chain maps. -/
@[simp]
theorem linearHomCochainMap_comp (f : C ⟶ D) (g : D ⟶ E)
    (M : ModuleCat.{0} R) :
    DualComplexUniversalCoefficient.Cycles.linearHomCochainMap (f ≫ g) M =
      DualComplexUniversalCoefficient.Cycles.linearHomCochainMap g M ≫ DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M := by
  ext n φ
  rfl

/-- A pulled-back cocycle evaluates on a class by first pushing the class forward. -/
theorem evaluateLinearHomCocycle_naturality (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M) n)
    (z : C.homology n) :
    DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle C M n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n c) z =
      DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle D M n c ((HomologicalComplex.homologyMap f n) z) := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n z
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle_chainClass,
    DualComplexUniversalCoefficient.Cycles.evaluateLinearHomCocycle_chainClass]
  rfl

/-- The canonical pairing on actual cohomology and homology is natural for every
chain map, including degree zero. -/
theorem linearHomHomologyEvaluation_naturality (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M).homology n) (z : C.homology n) :
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation C M n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n) c) z =
      DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation D M n c ((HomologicalComplex.homologyMap f n) z) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M) n c
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n z
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class, DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation_class_class]
  rfl

/-- Naturality of canonical evaluation as equality of linear functionals. -/
theorem linearHomHomologyEvaluation_naturality_linearMap (f : C ⟶ D)
    (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DualComplexUniversalCoefficient.Cycles.linearHomCochainComplex D M).homology n) :
    DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation C M n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f M) n) c) =
      (DualComplexUniversalCoefficient.Cycles.linearHomHomologyEvaluation D M n c).comp
        (HomologicalComplex.homologyMap f n).hom := by
  ext z
  exact linearHomHomologyEvaluation_naturality f M n c z

end Evaluation

variable {F : Type} [Field F]
variable {C D : ChainComplex (ModuleCat.{0} F) ℕ}

/-- The canonical field universal-coefficient equivalence intertwines actual
cohomological pullback with precomposition by the actual map on homology. -/
theorem dualComplexUniversalCoefficientEquiv_naturality (f : C ⟶ D)
    (n : ℕ) (c : (DualComplexUniversalCoefficient.Cycles.dualCochainComplex D).homology n) :
    DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n
        ((HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f (ModuleCat.of F F)) n) c) =
      (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv D n c).comp
        (HomologicalComplex.homologyMap f n).hom :=
  linearHomHomologyEvaluation_naturality_linearMap f (ModuleCat.of F F) n c

/-- The inverse universal-coefficient equivalence is natural as well; extending a
functional introduces no choice into its cohomology class. -/
theorem dualComplexUniversalCoefficientEquiv_symm_naturality (f : C ⟶ D)
    (n : ℕ) (L : Module.Dual F (D.homology n)) :
    (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n).symm
        (L.comp (HomologicalComplex.homologyMap f n).hom) =
      (HomologicalComplex.homologyMap (DualComplexUniversalCoefficient.Cycles.linearHomCochainMap f (ModuleCat.of F F)) n)
        ((DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv D n).symm L) := by
  apply (DualComplexUniversalCoefficient.Cycles.dualComplexUniversalCoefficientEquiv C n).injective
  rw [LinearEquiv.apply_symm_apply, dualComplexUniversalCoefficientEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DualComplexNaturality.Cycles
