import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Simplex Fillings -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles

noncomputable section

/-!
# Actual singular-chain fillings in a standard topological simplex

Positive cycles are filled using the proved singular homology vanishing of a
contractible space and the proved cycle/boundary quotient description.
Degree-zero fillings use the actual canonical homology augmentation, not an
assumed acyclic-model property.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

/-- Regard any zero-chain as a cycle in the genuine nonnegative chain complex. -/
def zeroChainToCycles (X : TopCat.{0}) :
    (LocalHomology.Cycles.integralSingularChains X).X 0 →+
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.integralSingularChains X) 0 where
  toFun c := ⟨c, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (LocalHomology.Cycles.integralSingularChains X) c⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The augmentation of genuine singular zero-chains is the canonical
homology augmentation composed with the canonical class projection. -/
def singularZeroChainAugmentation (X : TopCat.{0}) :
    (LocalHomology.Cycles.integralSingularChains X).X 0 →+ ℤ :=
  (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)).hom.toAddMonoidHom.comp
    ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.integralSingularChains X) 0).toAddMonoidHom.comp
      (zeroChainToCycles X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit zero-chain class is the canonical projection through the
degree-zero cycle isomorphism. -/
theorem zeroChain_class_eq (X : TopCat.{0}) (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.integralSingularChains X) 0 (zeroChainToCycles X c) =
      ((LocalHomology.Cycles.integralSingularChains X).homologyπ 0)
        ((LocalHomology.Cycles.integralSingularChains X).cycles₀Iso.inv c) := by
  let C := LocalHomology.Cycles.integralSingularChains X
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  apply congrArg (C.homologyπ 0)
  apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
  change (((C.sc 0).moduleCatCyclesIso.inv ≫ (C.sc 0).iCycles)
    (zeroChainToCycles X c)) = ((C.cycles₀Iso.inv ≫ C.cycles₀Iso.hom) c)
  rw [(C.sc 0).moduleCatCyclesIso_inv_iCycles, Iso.inv_hom_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual singular zero-simplex contributes its coefficient to the
augmentation; hence this is the usual sum-of-coefficients augmentation. -/
@[simp] theorem singularZeroChainAugmentation_simplex (X : TopCat.{0})
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋0⦌)) (a : ℤ) :
    singularZeroChainAugmentation X
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ a) = a := by
  let C := LocalHomology.Cycles.integralSingularChains X
  let ι := (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
  have hlift : ι ≫ C.cycles₀Iso.inv =
      C.liftCycles ι 0 (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    rw [HomologicalComplex.liftCycles_i, Category.assoc]
    change ι ≫ (C.cycles₀Iso.inv ≫ C.cycles₀Iso.hom) = ι
    rw [Iso.inv_hom_id, Category.comp_id]
  have h : (ι ≫ C.cycles₀Iso.inv) ≫ C.homologyπ 0 ≫
      X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) = 𝟙 _ := by
    rw [hlift]
    exact (TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
      (ModuleCat.of ℤ ℤ) σ
  have ha := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom a) h
  change (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)).hom
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C 0 (zeroChainToCycles X (ι a))) = a
  rw [zeroChain_class_eq]
  exact ha

/-- Every positive-degree singular cycle on a contractible space is the
boundary of an actual singular chain one degree higher. -/
theorem exists_singularBoundary_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0)
    (c : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.integralSingularChains X) n) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X (n + 1),
      (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b = c.1 := by
  let := ModuleCat.subsingleton_of_isZero
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible X n hn)
  exact (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ n c).mp (Subsingleton.elim _ _)

/-- Unbundled positive-cycle filling, directly in the singular chain modules. -/
theorem exists_singularBoundary_succ_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) b = c :=
  exists_singularBoundary_of_contractible X (n + 1) (Nat.succ_ne_zero n)
    ⟨c, (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ n c).mpr hc⟩

/-- A zero-chain with zero canonical augmentation on a path-connected space
is the boundary of an actual one-chain. -/
theorem exists_singularBoundary_zero_of_pathConnected
    (X : TopCat.{0}) [PathConnectedSpace X]
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0)
    (hc : singularZeroChainAugmentation X c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X 1,
      (LocalHomology.Cycles.integralSingularChains X).d 1 0 b = c := by
  apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ 0 (zeroChainToCycles X c)).mp
  apply (ContractibleModel.Cycles.integralSingularH0Iso X).toLinearEquiv.injective
  change singularZeroChainAugmentation X c = (ContractibleModel.Cycles.integralSingularH0Iso X).toLinearEquiv 0
  rw [hc, map_zero]

/-- The ordinary geometric standard simplex is contractible by convexity. -/
theorem stdSimplex_contractible (q : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (q + 1))) :=
  inferInstance

/-- The actual standard simplex object used by mathlib's singular-set
construction is contractible, including its universe-lift convention. -/
theorem toTopSimplex_contractible (q : ℕ) :
    ContractibleSpace (SimplexCategory.toTop.{0}.obj ⦋q⦌) := by
  let : ContractibleSpace (SimplexCategory.toTop₀.obj ⦋q⦌) := stdSimplex_contractible q
  exact (SimplexCategory.toTop₀.obj ⦋q⦌).uliftFunctorObjHomeo.symm.contractibleSpace

/-- Positive singular cycles in a geometric standard simplex have fillings. -/
theorem exists_stdSimplex_boundary_succ (q n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d
      (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d
        (n + 2) (n + 1) b = c := by
  let := stdSimplex_contractible q
  exact exists_singularBoundary_succ_of_contractible _ n c hc

/-- Positive singular cycles in the standard simplex object have actual
singular-chain fillings, suitable for acyclic-model recursion. -/
theorem exists_simplex_boundary_succ (q n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d
      (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d
        (n + 2) (n + 1) b = c := by
  let := toTopSimplex_contractible q
  exact exists_singularBoundary_succ_of_contractible _ n c hc

/-- Augmentation-zero singular zero-chains in the standard simplex have
actual one-chain fillings. -/
theorem exists_simplex_boundary_zero (q : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X 0)
    (hc : singularZeroChainAugmentation (SimplexCategory.toTop.{0}.obj ⦋q⦌) c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X 1,
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d 1 0 b = c :=
  exists_singularBoundary_zero_of_pathConnected _ c hc

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles
