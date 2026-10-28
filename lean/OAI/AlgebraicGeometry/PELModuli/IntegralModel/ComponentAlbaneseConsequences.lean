import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteComplexAlbaneseFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Total
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenerationFromAlbanese
import OAI.AlgebraicGeometry.AbelianVariety.PowerImage
import OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible

/-! # Component Albanese Consequences -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Native component geometry and the constructed Albanese properties
imply the exact total H¹ isomorphism and uniform geometric-fiber generation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem Components.ComponentAlbaneseData.target_points_pathConnected
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (j : Fin r)
    [Smooth (D.A j).X.hom] [IsProper (D.A j).X.hom] [GeometricallyConnected (D.A j).X.hom] :
    PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.complexAbelian c j).X) := by
  let A := D.targetComplexVariety c j
  have : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  have : LocallyPathConnectedSpace A.variety.analyticSpace :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  change PathConnectedSpace A.variety.analyticSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

theorem Components.ComponentAlbaneseData.total_h1_of_component_geometry
    (hHodgeComparison : AlbaneseCohomology.HodgeComparisonInput) {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (e : (∐ D.S) ≅ T)
    (hS : ∀ j, Smooth (D.S j).hom ∧ IsProper (D.S j).hom ∧ Components.RelativelyProjective (D.S j) ∧ GeometricallyConnected (D.S j).hom)
    (hA : ∀ j, Smooth (D.A j).X.hom ∧ IsProper (D.A j).X.hom ∧ GeometricallyConnected (D.A j).X.hom)
    (hAlb : ∀ j, D.IsComplexAlbanese c j) :
    Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (D.totalComplexMap c e)).hom := by
  have : ∀ j, Smooth (D.S j).hom := fun j => (hS j).1
  have : ∀ j, IsProper (D.S j).hom := fun j => (hS j).2.1
  have : ∀ j, GeometricallyConnected (D.S j).hom := fun j => (hS j).2.2.2
  have : ∀ j, Smooth (D.A j).X.hom := fun j => (hA j).1
  have : ∀ j, IsProper (D.A j).X.hom := fun j => (hA j).2.1
  have : ∀ j, GeometricallyConnected (D.A j).X.hom := fun j => (hA j).2.2
  let : ∀ j n, FiniteDimensional ℚ (Product.bettiQ (D.complexAbelian c j).X n) := fun j n =>
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite
      (D.targetComplexVariety c j).variety.presentation n
  let : ∀ j, PathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.complexAbelian c j).X) :=
    fun j => D.target_points_pathConnected c j
  apply D.totalComplexMap_h1_bijective c e
  intro j
  exact Total.albanese_h1_bijective hHodgeComparison (D.sourceComplexVariety c j (hS j).2.2.1)
    (D.complexBasePoint c j) (D.targetComplexVariety c j) (D.complexMap c j)
    (D.native_complex_albanese c j (hS j).2.2.1 (hAlb j))

theorem Components.ComponentAlbaneseData.generation_of_component_geometry
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) [IsDominant c]
    (hS : ∀ j, Smooth (D.S j).hom ∧ IsProper (D.S j).hom ∧ Components.RelativelyProjective (D.S j) ∧ GeometricallyConnected (D.S j).hom)
    (hA : ∀ j, Smooth (D.A j).X.hom ∧ IsProper (D.A j).X.hom ∧ GeometricallyConnected (D.A j).X.hom)
    (hAlb : ∀ j, D.IsComplexAlbanese c j) (j : Fin r) :
    ∃ n : ℕ, 0 < n ∧ ∀ t : Base.GeometricPoint B, Function.Surjective (D.sumOfDifferences j n t) := by
  have : Smooth (D.S j).hom := (hS j).1
  have : IsProper (D.S j).hom := (hS j).2.1
  have : GeometricallyConnected (D.S j).hom := (hS j).2.2.2
  have : Smooth (D.A j).X.hom := (hA j).1
  have : IsProper (D.A j).X.hom := (hA j).2.1
  have : GeometricallyConnected (D.A j).X.hom := (hA j).2.2
  let X := D.sourceComplexVariety c j (hS j).2.2.1
  let A := D.targetComplexVariety c j
  let eX : D.complexSurface c j ≅ X.toOver := Iso.refl _
  let eA : (D.complexAbelian c j).X ≅ A.toOver := Iso.refl _
  have : IsMonHom eA.hom := inferInstanceAs (IsMonHom (𝟙 (D.complexAbelian c j).X))
  exact D.uniform_generation_of_complex_albanese c j X A eX eA (D.complexBasePoint c j)
    (D.complexMap c j) (by simp [eX, eA])
    (D.native_complex_albanese c j (hS j).2.2.1 (hAlb j))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
