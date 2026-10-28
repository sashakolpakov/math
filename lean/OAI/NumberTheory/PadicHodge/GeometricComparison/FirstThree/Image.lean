import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexMap
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Image.FirstThreeHodgeImage

noncomputable section

/-! The first-three-term equivalence carries the original Hodge truncation images to their native counterparts. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

universe u v w

variable (R : Type*) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C]
  (A : C)

local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneTransport.FirstThreeHOneTransport.derived (C := C)

abbrev hom (K : CochainComplex C ℕ) := (DerivedCategory.singleFunctor C 0).obj A ⟶ (D).obj K

def map {K L : CochainComplex C ℕ} (f : K ⟶ L) : hom A K →ₗ[R] hom A L :=
  Linear.rightComp R _ ((D).map f)

def filtrationMap (K : CochainComplex C ℕ) (r : ℤ) : hom A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) →ₗ[R] hom A K :=
  FirstThreeHodgeImage.map R A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)

def filtration (K : CochainComplex C ℕ) (r : ℤ) : Submodule R (hom A K) :=
  LinearMap.range (filtrationMap R A K r)

def projectionEquiv (K : CochainComplex C ℕ) : hom A K ≃ₗ[R] hom A (ThreeComplex.FirstThreeComplex.complex K) :=
  LinearEquiv.ofBijective (FirstThreeHodgeImage.map R A (ThreeComplex.FirstThreeComplex.projection K)) (OneEquivalence.FirstThreeComplex.hone_bijective K A)

def hodgeProjectionEquiv (K : CochainComplex C ℕ) (r : ℤ) :
    hom A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) ≃ₗ[R] hom A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (ThreeComplex.FirstThreeComplex.complex K) r) :=
  LinearEquiv.ofBijective (FirstThreeHodgeImage.map R A (ComplexMap.HodgeComplexMap.map (ThreeComplex.FirstThreeComplex.projection K) r))
    (ComplexMap.HodgeComplexMap.projection_hone_bijective A K r)

theorem projection_filtrationMap (K : CochainComplex C ℕ) (r : ℤ) (x : hom A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)) :
    projectionEquiv R A K (filtrationMap R A K r x) =
      filtrationMap R A (ThreeComplex.FirstThreeComplex.complex K) r (hodgeProjectionEquiv R A K r x) := by
  change (x ≫ (D).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) ≫ (D).map (ThreeComplex.FirstThreeComplex.projection K) =
    (x ≫ (D).map (ComplexMap.HodgeComplexMap.map (ThreeComplex.FirstThreeComplex.projection K) r)) ≫
      (D).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (ThreeComplex.FirstThreeComplex.complex K) r)
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ComplexMap.HodgeComplexMap.inclusion]

theorem projection_filtration (K : CochainComplex C ℕ) (r : ℤ) :
    (filtration R A K r).map (projectionEquiv R A K).toLinearMap =
      filtration R A (ThreeComplex.FirstThreeComplex.complex K) r := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨hodgeProjectionEquiv R A K r x, (projection_filtrationMap R A K r x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (hodgeProjectionEquiv R A K r).surjective x
    exact ⟨filtrationMap R A K r z, ⟨z, rfl⟩, projection_filtrationMap R A K r z⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Image.FirstThreeHodgeImage
