import OAI.AlgebraicGeometry.DivisorClass.Chern.CombinedComplexSphereMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarRelativeBoundaryNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSphereComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.DiskProductSphereGenerator

/-! # Disk Product Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskProductGenerator

noncomputable section

section

/-! The actual complex product coordinate map carries the original relative
boundary to the already normalized real product sphere boundary. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def fullPlaneProductComplexMap (p : ℕ) :
    TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2))) ⟶
      TopCat.of (Fin (p + 2) → ℂ) :=
  TopCat.ofHom ⟨ProductRealCoordinates.fullPlaneProductComplexCoordinates p, (ProductRealCoordinates.fullPlaneProductComplexCoordinates p).continuous⟩

theorem fullPlaneProductComplexMap_puncture (p : ℕ) :
    Set.MapsTo (fullPlaneProductComplexMap p) ({0}ᶜ)
      ({0}ᶜ : Set (Fin (p + 2) → ℂ)) := by
  intro x hx he
  exact hx ((ProductRealCoordinates.fullPlaneProductComplexCoordinates p).injective (he.trans (map_zero _).symm))

theorem fullPlaneProductComplexMap_radial (p : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (fullPlaneProductComplexMap p) (fullPlaneProductComplexMap_puncture p) ≫
      TopCat.ofHom ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (ProductRealCoordinates.combinedComplexRealCoordinates p),
        (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (ProductRealCoordinates.combinedComplexRealCoordinates p)).continuous⟩ ≫
      TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 4)))) =
      PlaneProductTo.fullPlaneProductRadialMap (2 * p + 2) := by
  apply TopCat.ext
  intro x
  apply congrArg (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 4))))
  exact Subtype.ext (ProductRealCoordinates.fullPlaneProductComplexCoordinates_real p x.val)

theorem fullPlaneProductComplexMap_sphere_homology (p : ℕ) :
    homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (fullPlaneProductComplexMap p)
      (fullPlaneProductComplexMap_puncture p)) (2 * p + 4) ≫ CombinedComplexSphereMap.combinedComplexRationalSphereMap p =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ
        (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ)).δ
          (2 * p + 4) (2 * p + 3) rfl ≫
        homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap (2 * p + 2)))
          (2 * p + 3) := by
  let a := homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (fullPlaneProductComplexMap p) (fullPlaneProductComplexMap_puncture p))) (2 * p + 3)
  let b := homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (TopCat.ofHom ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (ProductRealCoordinates.combinedComplexRealCoordinates p),
      (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (ProductRealCoordinates.combinedComplexRealCoordinates p)).continuous⟩)) (2 * p + 3)
  let c := homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 4)))))) (2 * p + 3)
  have hr : a ≫ b ≫ c =
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap (2 * p + 2)))
        (2 * p + 3) := by
    dsimp only [a, b, c]
    rw [← homologyMap_comp, ← CategoryTheory.Functor.map_comp,
      ← homologyMap_comp, ← CategoryTheory.Functor.map_comp, fullPlaneProductComplexMap_radial]
  have hn := ScalarRelativeBoundaryNaturality.scalarRelativeBoundary_naturality ℚ (fullPlaneProductComplexMap p)
    (fullPlaneProductComplexMap_puncture p) (2 * p + 3)
  rw [CombinedComplexSphereMap.combinedComplexRationalSphereMap_formula]
  rw [← Category.assoc, ← Category.assoc, ← hn, Category.assoc, Category.assoc]
  exact congrArg (fun f => (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ
    (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ)).δ
      (2 * p + 4) (2 * p + 3) rfl ≫ f) hr

end

/-!
# ChernClass: the actual disk product represents the original complex generator

The original relative cross filling is carried through the actual
complex-linear line-plus-tangent coordinates. Its sphere boundary is
the original positive orthant generator; injectivity gives equality
with the original complex local class, with coefficient exactly one.
-/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def complexDiskProductFillingClass (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 2) → ℂ)) 0 (2 * p + 4) :=
  homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (fullPlaneProductComplexMap p)
    (fullPlaneProductComplexMap_puncture p)) (2 * p + 4)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
      (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ)) (2 * p + 4)
      (PlaneProductCycle.fullPlaneProductRelativeCycle (2 * p + 2) (2 * p) (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
        (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p))))

theorem complexDiskProductFillingClass_sphere (p : ℕ) :
    CombinedComplexSphereMap.combinedComplexRationalSphereMap p (complexDiskProductFillingClass p) =
      Rational.OrthantSphere.rationalOrthantSphereClass (2 * p + 3) := by
  have h := ConcreteCategory.congr_hom (fullPlaneProductComplexMap_sphere_homology p)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
      (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ)) (2 * p + 4)
      (PlaneProductCycle.fullPlaneProductRelativeCycle (2 * p + 2) (2 * p) (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
        (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p))))
  refine h.trans ?_
  have hz := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ (2 * p) _).mp
    (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).property
  exact (ProductSphereComparison.fullPlaneProductRelativeCycle_sphereBoundary (2 * p + 2) (2 * p)
    (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p)) (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val
    (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p)) hz).trans
      (DiskProductSphereGenerator.euclideanOrthantDiskProductSphere_eq_generator (2 * p))

theorem complexDiskProductFillingClass_eq_generatorClass (p : ℕ) :
    complexDiskProductFillingClass p = CombinedComplexSphereMap.combinedComplexRationalGeneratorClass p := by
  apply CombinedComplexSphereMap.combinedComplexRationalSphereMap_injective p
  rw [complexDiskProductFillingClass_sphere, CombinedComplexSphereMap.combinedComplexRationalGeneratorClass_sphere]

theorem complexDiskProductFillingClass_eq_originalGenerator (p : ℕ) :
    eqToHom (congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 2) → ℂ)) 0)
      (show 2 * p + 4 = 2 * (p + 2) by omega)) (complexDiskProductFillingClass p) =
      CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator (p + 2) := by
  rw [complexDiskProductFillingClass_eq_generatorClass]
  simpa only [CombinedComplexSphereMap.combinedComplexRationalGeneratorClass, Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass,
    Nat.mul_succ, id_eq, eqToHom_refl, ConcreteCategory.id_apply] using
      Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass_eq_originalGenerator (p + 1)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskProductGenerator
