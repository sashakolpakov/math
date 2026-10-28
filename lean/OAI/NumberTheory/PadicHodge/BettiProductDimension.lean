import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Betti Product Dimension -/

namespace OAI.NumberTheory.PadicHodge.BettiProductDimension.FrobeniusSlope

noncomputable section

/-! A dimension bound for the actual complex product, used without
transporting any operator identity through crystalline comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj

abbrev H1 (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) := AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X 1

def pullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) : H1 Y →ₗ[ℂ] H1 X :=
  (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f).hom

theorem pullback_id (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : pullback (𝟙 X) = LinearMap.id := by
  change ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) 1).map (𝟙 (Opposite.op X))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem pullback_comp {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullback f).comp (pullback g) = pullback (f ≫ g) := by
  change (((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) 1).map g.op) ≫
    ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) 1).map f.op)).hom = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

variable (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local notation "X" => A.toOver

def leftAxis : X ⟶ X ⊗ X := lift (𝟙 X) (1 : X ⟶ X)
def rightAxis : X ⟶ X ⊗ X := lift (1 : X ⟶ X) (𝟙 X)

def first : X ⊗ X ⟶ X ⊗ X := fst X X ≫ leftAxis A
def second : X ⊗ X ⟶ X ⊗ X := snd X X ≫ rightAxis A

theorem first_mul_second : first A * second A = 𝟙 (X ⊗ X) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]
    simp only [first, second, leftAxis, rightAxis, Category.assoc,
      lift_fst, MonObj.comp_one, Category.comp_id, Category.id_comp, _root_.mul_one]
  · rw [MonObj.mul_comp]
    simp only [first, second, leftAxis, rightAxis, Category.assoc,
      lift_snd, MonObj.comp_one, Category.comp_id, Category.id_comp, _root_.one_mul]

def projectionSum : H1 X × H1 X →ₗ[ℂ] H1 (X ⊗ X) :=
  (pullback (fst X X)).comp (LinearMap.fst ℂ _ _) +
    (pullback (snd X X)).comp (LinearMap.snd ℂ _ _)

theorem projectionSum_surjective : Function.Surjective (projectionSum A) := by
  have h := AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM.complex_pullback_mul_map (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A)
    (first A) (second A)
  change pullback (first A * second A) = pullback (first A) + pullback (second A) at h
  rw [first_mul_second, pullback_id] at h
  intro x
  refine ⟨(pullback (leftAxis A) x, pullback (rightAxis A) x), ?_⟩
  change pullback (fst X X) (pullback (leftAxis A) x) +
    pullback (snd X X) (pullback (rightAxis A) x) = x
  rw [← LinearMap.comp_apply, pullback_comp, ← LinearMap.comp_apply, pullback_comp]
  exact (LinearMap.congr_fun h x).symm

/-- The bound concerns the original cohomology spaces of the original schemes. -/
theorem product_finrank_le : Module.finrank ℂ (H1 (X ⊗ X)) ≤ 2 * Module.finrank ℂ (H1 X) := by
  let : FiniteDimensional ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  let : FiniteDimensional ℂ (H1 X) :=
    Module.Finite.equiv (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (AlgebraicGeometry.Betti.Scheme.schemePointSpace X) 1)
  have h := LinearMap.finrank_le_finrank_of_surjective (projectionSum_surjective A)
  rw [Module.finrank_prod] at h
  omega

end

end OAI.NumberTheory.PadicHodge.BettiProductDimension.FrobeniusSlope
