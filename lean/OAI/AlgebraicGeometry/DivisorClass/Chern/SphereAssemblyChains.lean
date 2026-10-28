import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly

/-! # Sphere Assembly Chains -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SphereAssemblyChains

noncomputable section

/-! The ordinary chain represented by the native sphere-cover assembly is the sum of its two chart chains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SphereRationalChainPieces

variable {m n : ℕ} (p : Rational.SphereAssembly.SphereRationalChainPieces m n)

local notation "CU" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantFirstChart m)
local notation "CV" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantSecondChart m)
local notation "S" => OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
  (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
local notation "j" => OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.binarySmallRationalChainInclusion (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
  (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))

def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly.SphereRationalChainPieces.ordinaryCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))) (n + 1) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (j) (n + 1) p.smallCycle

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly.SphereRationalChainPieces.ordinaryCycle_val :
    p.ordinaryCycle.val =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))))).f (n + 1) p.left +
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))))).f (n + 1) p.right := by
  have hl : (biprod.inl : CU ⟶ CU ⊞ CV) ≫ (S).g ≫ (j) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))) := by
    rw [AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence_g, biprod.inl_desc_assoc]
    exact AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.binarySmallRationalChainInclusion_left _ _ _
  have hr : (biprod.inr : CV ⟶ CU ⊞ CV) ≫ (S).g ≫ (j) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))) := by
    rw [AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence_g, biprod.inr_desc_assoc]
    exact AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.binarySmallRationalChainInclusion_right _ _ _
  have hL := ConcreteCategory.congr_hom (congrArg (fun f => f.f (n + 1)) hl) p.left
  have hR := ConcreteCategory.congr_hom (congrArg (fun f => f.f (n + 1)) hr) p.right
  change (j).f (n + 1) ((S).g.f (n + 1)
    ((biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) p.left + (biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) p.right)) = _
  rw [map_add, map_add]
  exact congrArg₂ (fun x y => x + y) hL hR

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly.SphereRationalChainPieces.sphereClass_eq_ordinaryCycle :
    p.sphereClass = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))) (n + 1) p.ordinaryCycle :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (j) (n + 1) p.smallCycle

end SphereRationalChainPieces

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SphereAssemblyChains
