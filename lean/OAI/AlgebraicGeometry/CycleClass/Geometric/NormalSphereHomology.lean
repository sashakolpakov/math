import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel

/-! # Normal Sphere Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology.Cycles

noncomputable section

/-!
# Singular homology of the punctured normal model

The actual radial homotopy equivalence identifies singular homology of the
punctured normal space with singular homology of its sphere. No computation of
sphere homology, orientation generator, or Thom class is assumed here.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {R : Type} [Ring R]

/-- Radial retraction gives a chain homotopy equivalence for genuine singular
chains with any coefficient module. -/
def normalSphereSingularChainsEquiv (M : ModuleCat.{0} R) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal E)))
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))) :=
  ContractibleModel.Cycles.singularChainsHomotopyEquiv M
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (NormalSphere.Cycles.normalSphereHomotopyEquiv E)

/-- The induced genuine singular-homology isomorphism from punctured normal
coordinates to the unit sphere. -/
def normalSphereSingularHomologyIso (M : ModuleCat.{0} R) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E)) :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv M
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (NormalSphere.Cycles.normalSphereHomotopyEquiv E) n

@[simp]
theorem normalSphereSingularHomologyIso_hom (M : ModuleCat.{0} R) (n : ℕ) :
    (normalSphereSingularHomologyIso E M n).hom =
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
        (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection E)) := rfl

@[simp]
theorem normalSphereSingularHomologyIso_inv (M : ModuleCat.{0} R) (n : ℕ) :
    (normalSphereSingularHomologyIso E M n).inv =
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
        (TopCat.ofHom (NormalSphere.Cycles.normalSphereInclusion E)) := rfl

/-- The integral specialization uses the same singular chains as the local
homology pair construction. -/
def normalSphereIntegralHomologyIso (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.PuncturedNormal E))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))).homology n :=
  normalSphereSingularHomologyIso E (ModuleCat.of ℤ ℤ) n

@[simp]
theorem normalSphereIntegralHomologyIso_hom (n : ℕ) :
    (normalSphereIntegralHomologyIso E n).hom =
      HomologicalComplex.homologyMap
        (LocalHomology.Cycles.integralSingularChainFunctor.map (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection E))) n := rfl

@[simp]
theorem normalSphereIntegralHomologyIso_inv (n : ℕ) :
    (normalSphereIntegralHomologyIso E n).inv =
      HomologicalComplex.homologyMap
        (LocalHomology.Cycles.integralSingularChainFunctor.map (TopCat.ofHom (NormalSphere.Cycles.normalSphereInclusion E))) n := rfl

/-- In the complex normal model this is the sphere step needed for the
relative pair `(C^p, C^p \ {0})`. -/
def complexNormalSphereIntegralHomologyIso (p n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ)))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)))).homology n :=
  normalSphereIntegralHomologyIso (Fin p → ℂ) n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology.Cycles
