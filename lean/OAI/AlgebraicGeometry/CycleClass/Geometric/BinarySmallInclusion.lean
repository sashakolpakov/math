import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage

/-! # Binary Small Inclusion -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles

noncomputable section

/-!
# The binary small-chain presentation and its canonical inclusion

This identifies the actual binary-cover model used by Mayer--Vietoris with
the actual Bool-indexed small-chain model used by subdivision.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) (A B : Set X)

/-- The binary small-chain model used by Mayer--Vietoris is the same actual
small-chain complex as the Bool-indexed cover model. -/
def binarySmallFamilyChainIso :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ≅
      SmallChainImage.Cycles.integralSmallSingularChains X (fun b : Bool => if b then B else A) :=
  eqToIso (congrArg
    (fun S : (TopCat.toSSet.obj X).Subcomplex =>
      (S : SSet).chainComplex (ModuleCat.of ℤ ℤ))
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq X A B))

/-- The actual binary-cover small-chain inclusion, using the proved equality
of its two presentations. -/
def binarySmallIntegralChainInclusion :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ⟶ LocalHomology.Cycles.integralSingularChains X :=
  (binarySmallFamilyChainIso X A B).hom ≫
    SmallChainImage.Cycles.smallIntegralChainInclusion X (fun b : Bool => if b then B else A)

private theorem chainInclusion_eq_transport {S : SSet.{0}} (P Q : S.Subcomplex)
    (h : P = Q) :
    (eqToIso (congrArg (fun T : S.Subcomplex =>
      (T : SSet).chainComplex (ModuleCat.of ℤ ℤ)) h)).hom ≫
      SSet.chainComplexMap Q.ι (ModuleCat.of ℤ ℤ) =
      SSet.chainComplexMap P.ι (ModuleCat.of ℤ ℤ) := by
  subst Q
  simp

/-- The transported binary inclusion is exactly the map induced by the
canonical simplicial-subcomplex inclusion. -/
theorem binarySmallIntegralChainInclusion_eq_canonical :
    binarySmallIntegralChainInclusion X A B =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι := by
  exact chainInclusion_eq_transport _ _ (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq X A B)

set_option backward.isDefEq.respectTransparency false in
/-- The left small-chain map followed by the ambient inclusion is the actual
singular chain map of the left subspace inclusion. -/
theorem binarySmallIntegralChainInclusion_left :
    SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X A B) ≫
      binarySmallIntegralChainInclusion X A B =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X A) := by
  rw [binarySmallIntegralChainInclusion_eq_canonical, ← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The right small-chain map followed by the ambient inclusion is the actual
singular chain map of the right subspace inclusion. -/
theorem binarySmallIntegralChainInclusion_right :
    SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X A B) ≫
      binarySmallIntegralChainInclusion X A B =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X B) := by
  rw [binarySmallIntegralChainInclusion_eq_canonical, ← CategoryTheory.Functor.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles
