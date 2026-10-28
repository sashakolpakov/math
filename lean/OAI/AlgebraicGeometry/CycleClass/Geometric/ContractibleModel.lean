import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Basic

/-! # Contractible Model -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles

noncomputable section

/-!
# Singular homology of contractible complex normal models

The chain and homology objects here are mathlib's genuine singular chains.
Continuous homotopy equivalences induce chain homotopy equivalences. Combining
this with the computation for a point proves positive-degree vanishing.

The complex normal model is the actual topological vector space `Fin p → ℂ`.
An explicit straight-line contraction is given. This file does not compute
its punctured-space or local homology and does not postulate an orientation
class or a cycle class map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

variable {R : Type} [Ring R]

/-- A genuine homotopy equivalence induces a homotopy equivalence of singular
chain complexes with the indicated coefficient module. -/
def singularChainsHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj X)
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj Y) where
  hom := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
    (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
    (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      H.singularChainComplexFunctorObjMap M
  homotopyInvHomId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      H.singularChainComplexFunctorObjMap M

/-- Singular homology is invariant under an actual continuous homotopy
equivalence. -/
def singularHomologyIsoOfHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj X ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj Y :=
  (singularChainsHomotopyEquiv M e).toHomologyIso n

/-- Positive-degree singular homology of a contractible space is zero. -/
theorem isZero_singularHomology_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj X) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} R) n M (TopCat.of Unit) hn).of_iso
      (singularHomologyIsoOfHomotopyEquiv M (Y := TopCat.of Unit) e n)

/-- The integral specialization, expressed in the absolute chain objects
used by the relative and local homology construction. -/
theorem isZero_integralSingularHomology_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((LocalHomology.Cycles.integralSingularChains X).homology n) :=
  isZero_singularHomology_of_contractible (ModuleCat.of ℤ ℤ) X n hn

/-- The genuine integral singular chain complex of a contractible space
is exact in every positive degree. -/
theorem integralSingularChains_exactAt_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (LocalHomology.Cycles.integralSingularChains X).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_integralSingularHomology_of_contractible X n hn

/-- The canonical augmentation computes integral H0 of a path-connected
space, with no choice of homology generator. -/
def integralSingularH0Iso (X : TopCat.{0}) [PathConnectedSpace X] :
    (LocalHomology.Cycles.integralSingularChains X).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  let e := asIso (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ))
  exact e

/-- Explicit straight-line contraction of the complex normal coordinate
space, starting with the identity and ending at the zero vector. -/
def complexNormalModelContraction (p : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Fin p → ℂ))
      (ContinuousMap.const (Fin p → ℂ) 0) where
  toFun q := (1 - (q.1 : ℝ)) • q.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

theorem complexNormalModelContraction_apply (p : ℕ)
    (t : unitInterval) (x : Fin p → ℂ) :
    complexNormalModelContraction p (t, x) = (1 - (t : ℝ)) • x := rfl

/-- The complex normal coordinate space is contractible through the displayed
straight-line contraction. -/
theorem complexNormalModel_contractible (p : ℕ) : ContractibleSpace (Fin p → ℂ) :=
  (contractible_iff_id_nullhomotopic (Fin p → ℂ)).mpr
    ⟨0, ⟨complexNormalModelContraction p⟩⟩

/-- Positive-degree integral homology vanishes on the complex normal model. -/
theorem isZero_complexNormalModelHomology (p n : ℕ) (hn : n ≠ 0) :
    IsZero ((LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).homology n) := by
  let := complexNormalModel_contractible p
  exact isZero_integralSingularHomology_of_contractible _ n hn

/-- The integral singular chain complex of the normal model is exact in
positive degrees. -/
theorem complexNormalModel_exactAt (p n : ℕ) (hn : n ≠ 0) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_complexNormalModelHomology p n hn

/-- Degree-zero homology of the normal model is canonically the integers. -/
def complexNormalModelH0Iso (p : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).homology 0 ≅ ModuleCat.of ℤ ℤ :=
  integralSingularH0Iso _

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles
