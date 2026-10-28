import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing
import Mathlib.Analysis.Convex.Contractible

/-! # Real Local Homology -/

namespace OAI.AlgebraicTopology.Duality.RealLocalHomology.Constructions.PoincarePairing

noncomputable section

/-! PoincarePairing: local homology vanishes outside the dimension of real Euclidean space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integralH0Map_isIso {X Y : TopCat.{0}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) :
    IsIso (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0) := by
  let : IsIso (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 ≫
      Y.singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    rw [AlgebraicGeometry.CycleClass.Geometric.HomologyZeroNaturality.Cycles.integralSingularH0_augmentation_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0)
    (Y.singularHomology₀ε (ModuleCat.of ℤ ℤ))

theorem relativeH0_isZero_of_nonempty (X : TopCat.{0}) [PathConnectedSpace X]
    (A : Set X) [Nonempty A] : IsZero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A 0) := by
  let x : A := Classical.choice inferInstance
  let f : TopCat.of PUnit ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const PUnit x)
  have hcomp : AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 ≫ AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0 =
      AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (f ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) 0 := by
    change HomologicalComplex.homologyMap _ 0 ≫ HomologicalComplex.homologyMap _ 0 = _
    rw [← HomologicalComplex.homologyMap_comp, ← AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_comp]
  let : IsIso (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (f ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) 0) :=
    integralH0Map_isIso _
  let : Epi (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 ≫ AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0) := by
    rw [hcomp]
    infer_instance
  let : Epi (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0) :=
    epi_of_epi (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0) _
  apply IsZero.of_epi_eq_zero (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyProjection X A 0)
  exact zero_of_epi_comp (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.subspaceHomologyInclusion X A 0)
    (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.subspaceHomologyInclusion_projection X A 0)

theorem realEuclideanLocalHomology_isZero (n p : ℕ) (hp : p ≠ n) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) 0 p) := by
  cases n with
  | zero =>
    have hEmpty : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) = ∅ := by
      ext x
      simp [Subsingleton.elim x 0]
    unfold AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology
    rw [hEmpty]
    exact (AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible
      (TopCat.of (EuclideanSpace ℝ (Fin 0))) p hp).of_iso
        (AlgebraicGeometry.CycleClass.Geometric.Point.Cycles.relativeEmptyHomologyIso (TopCat.of (EuclideanSpace ℝ (Fin 0))) p)
  | succ n =>
    let E := EuclideanSpace ℝ (Fin (n + 1))
    cases p with
    | zero =>
      let : Nonempty (({0}ᶜ : Set E)) := by
        obtain ⟨x, hx⟩ := exists_ne (0 : E)
        exact ⟨⟨x, hx⟩⟩
      exact relativeH0_isZero_of_nonempty (TopCat.of E) {0}ᶜ
    | succ p =>
      cases p with
      | zero =>
        have hdim : 1 < Module.finrank ℝ E := by
          change 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
          simp only [finrank_euclideanSpace_fin]
          omega
        let : PathConnectedSpace (({0}ᶜ : Set E)) :=
          isPathConnected_iff_pathConnectedSpace.mp
            (isPathConnected_compl_singleton_of_one_lt_rank
              (Module.one_lt_rank_of_one_lt_finrank hdim) 0)
        exact AlgebraicGeometry.CycleClass.Geometric.ComplexLocalVanishing.Cycles.relativeH1_isZero_of_pathConnected (TopCat.of E) {0}ᶜ
          (AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible (TopCat.of E) 1 (by decide))
      | succ p =>
        let e := AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundaryIso (TopCat.of E) ({0}ᶜ : Set E) (p + 1)
          (AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible (TopCat.of E) (p + 1 + 1)
            (Nat.succ_ne_zero _))
          (AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible (TopCat.of E) (p + 1)
            (Nat.succ_ne_zero _)) ≪≫ AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology.Cycles.normalSphereIntegralHomologyIso E (p + 1)
        exact (AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereHomology_isZero n (p + 1) (Nat.succ_ne_zero _) (by omega)).of_iso e

end

end OAI.AlgebraicTopology.Duality.RealLocalHomology.Constructions.PoincarePairing
