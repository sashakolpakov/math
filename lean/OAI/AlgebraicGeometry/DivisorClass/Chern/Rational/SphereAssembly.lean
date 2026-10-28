import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives
import OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

/-! # Sphere Assembly -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly

noncomputable section

/-!
# ChernClass: assemble specified rational chart chains through the native sphere sequence

The input consists of actual chart chains and their proved opposite
boundaries. The resulting class and connecting formula are constructed
from the existing small-chain exact sequence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure SphereRationalChainPieces (m n : ℕ) where
  left : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantFirstChart m)).X (n + 1)
  right : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSecondChart m)).X (n + 1)
  overlap : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap m)) n
  left_boundary : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantFirstChart m)).d (n + 1) n left =
    -(((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion m)).f n overlap.val)
  right_boundary : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSecondChart m)).d (n + 1) n right =
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion m)).f n overlap.val

namespace SphereRationalChainPieces

variable {m n : ℕ} (p : SphereRationalChainPieces m n)

local notation "CU" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantFirstChart m)
local notation "CV" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantSecondChart m)
local notation "S" => OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
  (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
local notation "jU" => CategoryTheory.Functor.map (OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion m)
local notation "jV" => CategoryTheory.Functor.map (OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion m)

def middle : (S).X₂.X (n + 1) :=
  (biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) p.left + (biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) p.right

theorem middle_boundary : (S).f.f n (-p.overlap.val) = (S).X₂.d (n + 1) n p.middle := by
  have hf : (S).f = (jU) ≫ (biprod.inl : CU ⟶ CU ⊞ CV) -
      (jV) ≫ (biprod.inr : CV ⟶ CU ⊞ CV) := by
    simp only [AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence_f, biprod.lift_eq, Preadditive.neg_comp,
      sub_eq_add_neg, OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion, OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion]
    rfl
  have hl := ConcreteCategory.congr_hom ((biprod.inl : CU ⟶ CU ⊞ CV).comm (n + 1) n) p.left
  have hr := ConcreteCategory.congr_hom ((biprod.inr : CV ⟶ CU ⊞ CV).comm (n + 1) n) p.right
  change (CU ⊞ CV).d (n + 1) n ((biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) _) =
    (biprod.inl : CU ⟶ CU ⊞ CV).f n ((CU).d (n + 1) n _) at hl
  change (CU ⊞ CV).d (n + 1) n ((biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) _) =
    (biprod.inr : CV ⟶ CU ⊞ CV).f n ((CV).d (n + 1) n _) at hr
  change (S).f.f n (-p.overlap.val) = (CU ⊞ CV).d (n + 1) n p.middle
  rw [SphereRationalChainPieces.middle, map_add, hl, hr, p.left_boundary, p.right_boundary, hf]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_sub, LinearMap.sub_apply, ConcreteCategory.comp_apply, map_neg]
  abel

def smallCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (S).X₃ (n + 1) :=
  ⟨(S).g.f (n + 1) p.middle, by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((S).g.comm (n + 1) n) p.middle
    change (S).X₃.d (n + 1) n ((S).g.f (n + 1) _) =
      (S).g.f n ((S).X₂.d (n + 1) n p.middle) at h
    rw [← p.middle_boundary] at h
    exact h.trans (ConcreteCategory.congr_hom (congrArg (fun f => f.f n) (S).zero) (-p.overlap.val))⟩

def sphereClass : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))).homology (n + 1) :=
  HomologicalComplex.homologyMap (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.binarySmallRationalChainInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))) (n + 1)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (S).X₃ (n + 1) p.smallCycle)

theorem sphereClass_boundary :
    AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) n p.sphereClass =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap m)) n (-p.overlap) := by
  apply AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary_eq_of_lift (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) n
    p.smallCycle p.middle (-p.overlap) rfl
  exact p.middle_boundary

end SphereRationalChainPieces

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly
