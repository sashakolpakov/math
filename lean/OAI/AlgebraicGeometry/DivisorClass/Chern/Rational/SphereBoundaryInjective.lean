import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDoubleBoundary

/-! # Sphere Boundary Injective -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereBoundaryInjective

noncomputable section

/-!
# ChernClass: the native rational sphere boundary detects positive-degree classes

The two pole charts are contractible. Exactness therefore makes the
Mayer–Vietoris boundary injective, and the specified overlap retraction
is an actual homotopy equivalence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalSphereLowerMap_injective (m n : ℕ) :
    Function.Injective (ProductDoubleBoundary.rationalSphereLowerMap m n) := by
  let X := CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)
  let U := CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))
  let V := CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))
  let := CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_contractible (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))
  let := CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_contractible (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))
  have hU : IsZero ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).homology (n + 1)) :=
    CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ)
      (TopCat.of U) (n + 1) (Nat.succ_ne_zero n)
  have hV : IsZero ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V)).homology (n + 1)) :=
    CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ)
      (TopCat.of V) (n + 1) (Nat.succ_ne_zero n)
  have hsum : AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisSum X U V (n + 1) = 0 :=
    ((biprod_isZero_iff _ _).mpr ⟨hU, hV⟩).eq_zero_of_src _
  have hmono : Mono (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary X U V
      (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) n) :=
    (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietoris_exact_ambient X U V
      (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) n).mono_g hsum
  let e := CycleClass.Geometric.ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℚ ℚ)
    (X := TopCat.of (U ∩ V : Set X)) (Y := CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m)
    (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (m + 1)) n
  have he : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  exact he.comp ((ModuleCat.mono_iff_injective _).mp hmono)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereBoundaryInjective
