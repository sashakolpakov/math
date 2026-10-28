import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCap

/-! # Small Supported Cap Boundary -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapBoundary

noncomputable section

/-!
# Boundary formula for the cap product on small chains

The cap product constructed using the actual binary small-chain pushout
satisfies the usual signed boundary formula already inside the first piece.
The proof uses injectivity of its inclusion into the ambient rational chains.
No openness, covering, or excision hypotheses are needed for these identities.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Degree transport in the actual binary small-chain complex. -/
abbrev binarySmallChainCast (X : TopCat.{0}) (U A : Set X)
    {m n : ℕ} (h : m = n) :
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X m →ₗ[ℤ]
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X n :=
  Products.Cap.chainCast (R := ℤ) (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X U A : SSet) h

/-- Ambient inclusion commutes with degree transport of small chains. -/
theorem binarySmallIntegralChainInclusion_chainCast
    (X : TopCat.{0}) (U A : Set X) {m n : ℕ} (h : m = n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f n (binarySmallChainCast X U A h z) =
      Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X) h
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f m z) := by
  subst n
  rfl

/-- The differential of a degree-transported small chain is the same
native differential before transport. -/
theorem boundary_binarySmallChainCast (X : TopCat.{0}) (U A : Set X)
    {m n : ℕ} (h : m = n) (k : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d n k (binarySmallChainCast X U A h z) =
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d m k z := by
  subst n
  rfl

/-- Degree transport of a small cycle agrees with transport of its chain. -/
theorem binarySmallCycleDegreeCast_val (X : TopCat.{0}) (U A : Set X)
    {m n : ℕ} (h : m = n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) m) :
    ((h ▸ z) : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) n).val =
      binarySmallChainCast X U A h z.val := by
  subst n
  rfl

/-- The signed cap boundary identity holds in the rational chains of the
first piece, rather than only after ambient inclusion. -/
theorem smallSupportedCap_boundary (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q + 1)) :
    SmallSupportedCap.smallSupportedCap X U A p q c
        ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d (p + q + 1) (p + q) z) =
      SmallSupportedCap.smallSupportedCap X U A (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (binarySmallChainCast X U A (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z)) := by
  have hZ := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).comm (p + q + 1) (p + q)) z
  have hU := ConcreteCategory.congr_hom
    ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).comm (q + 1) q)
    (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z)
  have hC := ConcreteCategory.congr_hom
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).comm p (p + 1)) c
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d (p + q + 1) (p + q) z) at hZ
  change (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
      ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f (q + 1)
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z)) =
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f q
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z)) at hU
  change (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) =
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c) at hC
  apply SmallSupportedCap.rationalSubspaceChainInclusion_injective X U q
  rw [map_add, map_zsmul, SmallSupportedCap.smallSupportedCap_inclusion, SmallSupportedCap.smallSupportedCap_inclusion,
    ← hU, SmallSupportedCap.smallSupportedCap_inclusion, ← hZ,
    binarySmallIntegralChainInclusion_chainCast, ← hC]
  exact IntegralCapCoefficients.mixedSingularCap_boundary X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
    ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A).f (p + q + 1) z)

/-- The same identity solved for the boundary of the local cap product. -/
theorem boundary_smallSupportedCap (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).X (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (SmallSupportedCap.smallSupportedCap X U A p q c
            ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A).d (p + q + 1) (p + q) z) -
          SmallSupportedCap.smallSupportedCap X U A (p + 1) q
            ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
            (binarySmallChainCast X U A (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [smallSupportedCap_boundary, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

/-- On a small cycle, the local cap intertwines coboundary and boundary
with the sign used by the connecting homomorphism. -/
theorem smallSupportedCap_boundary_cycle (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)).d (q + 1) q
        (SmallSupportedCap.smallSupportedCap X U A p (q + 1) c z.val) =
      ((-1 : ℤ) ^ (p + 1)) • SmallSupportedCap.smallSupportedCap X U A (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (binarySmallChainCast X U A (by omega : p + q + 1 = (p + 1) + q) z.val) := by
  rw [boundary_smallSupportedCap,
    Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) (p + q + 1) (p + q) z,
    map_zero, zero_sub, pow_succ, mul_smul, neg_one_smul]

/-- A relative cocycle caps a small cycle to an actual rational cycle
on the first piece, including in output degree zero. -/
theorem smallSupportedCap_mem_chainCycles (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) (p + q)) :
    SmallSupportedCap.smallSupportedCap X U A p q c.val z.val ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q := by
  cases q with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ q =>
    apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q _).mpr
    rw [boundary_smallSupportedCap X U A p q c.val z.val]
    have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A)
      (p + q + 1) (p + q) z
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
      p (p + 1) c
    simp only [hz, hc, map_zero, LinearMap.zero_apply, sub_self, smul_zero]

/-- The local cap restricted to genuine cocycles and small cycles. -/
def smallSupportedCapCycles (X : TopCat.{0}) (U A : Set X) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p →ₗ[ℚ]
      (Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) (p + q) →ₗ[ℤ]
        Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of U)) q) where
  toFun c := {
    toFun := fun z => ⟨SmallSupportedCap.smallSupportedCap X U A p q c.val z.val,
      smallSupportedCap_mem_chainCycles X U A p q c z⟩
    map_add' := by
      intro z w
      apply Subtype.ext
      exact (SmallSupportedCap.smallSupportedCap X U A p q c.val).map_add z.val w.val
    map_smul' := by
      intro r z
      apply Subtype.ext
      change SmallSupportedCap.smallSupportedCap X U A p q c.val (r • z.val) =
        r • SmallSupportedCap.smallSupportedCap X U A p q c.val z.val
      simp only [map_zsmul] }
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change SmallSupportedCap.smallSupportedCap X U A p q (c.val + d.val) z.val =
      SmallSupportedCap.smallSupportedCap X U A p q c.val z.val + SmallSupportedCap.smallSupportedCap X U A p q d.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change SmallSupportedCap.smallSupportedCap X U A p q (r • c.val) z.val =
      r • SmallSupportedCap.smallSupportedCap X U A p q c.val z.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem smallSupportedCapCycles_val (X : TopCat.{0}) (U A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X U A) (p + q)) :
    (smallSupportedCapCycles X U A p q c z).val =
      SmallSupportedCap.smallSupportedCap X U A p q c.val z.val := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapBoundary
