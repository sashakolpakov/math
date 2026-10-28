import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallCochains
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupAssociativity

/-! # Binary Small Right Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions

noncomputable section

section

/-! Right multiplication by actual ordinary cochains on the two-support quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

theorem binarySmallCochainInclusion_restriction (U : Set X)
    (hU : CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U ≫ CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B = 0)
    (n : ℕ) (c : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f n
      (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c) = 0 := by
  apply (BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv (TopCat.of U) n).injective
  rw [map_zero]
  ext z
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj (TopCat.of U)) n
    ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U))).f n
      (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c)) z = 0
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_pullback]
  change BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv X n (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c)
    ((CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U).f n z) = 0
  rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_eval]
  have hz := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hU n) z
  exact (congrArg c hz).trans (map_zero c)

theorem binarySmallCup_restriction_zero (U : Set X)
    (hU : CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X U ≫ CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B = 0)
    {p q : ℕ} (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X U).f (p+q)
      (AlgebraicTopology.Products.Cup.singularCup X (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a) b) = 0 := by
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U)).f (p+q)
    (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ)
      (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a) b) = 0
  rw [CycleClass.Geometric.RelativeCup.Cycles.cupWith_singularPullback, binarySmallCochainInclusion_restriction X A B U hU,
    AlgebraicTopology.Products.Cup.cupWith_zero_left]

def binarySmallRightCupFn (p q : ℕ)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).X (p+q) :=
  BinarySmallCochains.Constructions.binarySmallCochainLift X A B (p+q)
    (AlgebraicTopology.Products.Cup.singularCup X (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a) b)
    (binarySmallCup_restriction_zero X A B A
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) a b)
    (binarySmallCup_restriction_zero X A B B
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) a b)

theorem binarySmallRightCupFn_inclusion (p q : ℕ)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (binarySmallRightCupFn X A B p q a b) =
      AlgebraicTopology.Products.Cup.singularCup X (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a) b :=
  BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion X A B (p+q) _
    (binarySmallCup_restriction_zero X A B A
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) a b)
    (binarySmallCup_restriction_zero X A B B
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) a b)

def binarySmallRightCup (p q : ℕ) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q →ₗ[ℚ]
        (BinarySmallCochains.Constructions.binarySmallCochains X A B).X (p+q) where
  toFun a := {
    toFun := binarySmallRightCupFn X A B p q a
    map_add' := by
      intro b c
      apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
      rw [map_add, binarySmallRightCupFn_inclusion, binarySmallRightCupFn_inclusion,
        binarySmallRightCupFn_inclusion]
      exact AlgebraicTopology.Products.Cup.cupWith_add_right (TopCat.toSSet.obj X)
        (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
        (LinearMap.mul ℚ ℚ) _ b c
    map_smul' := by
      intro r b
      apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
      rw [map_smul, binarySmallRightCupFn_inclusion, binarySmallRightCupFn_inclusion]
      exact AlgebraicTopology.Products.Cup.cupWith_smul_right (TopCat.toSSet.obj X)
        (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
        (LinearMap.mul ℚ ℚ) r _ b }
  map_add' := by
    intro a c
    ext b : 1
    apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
    change BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (binarySmallRightCupFn X A B p q (a+c) b) =
      BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q)
        (binarySmallRightCupFn X A B p q a b + binarySmallRightCupFn X A B p q c b)
    rw [map_add, binarySmallRightCupFn_inclusion, binarySmallRightCupFn_inclusion,
      binarySmallRightCupFn_inclusion, map_add]
    exact AlgebraicTopology.Products.Cup.cupWith_add_left (TopCat.toSSet.obj X)
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) _ _ b
  map_smul' := by
    intro r a
    ext b : 1
    apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q)
    change BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (binarySmallRightCupFn X A B p q (r • a) b) =
      BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (r • binarySmallRightCupFn X A B p q a b)
    rw [map_smul, binarySmallRightCupFn_inclusion, binarySmallRightCupFn_inclusion, map_smul]
    exact AlgebraicTopology.Products.Cup.cupWith_smul_left (TopCat.toSSet.obj X)
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) r _ b

theorem binarySmallRightCup_inclusion (p q : ℕ)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) (binarySmallRightCup X A B p q a b) =
      AlgebraicTopology.Products.Cup.singularCup X (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a) b :=
  binarySmallRightCupFn_inclusion X A B p q a b

def binarySmallCochainCast {m n : ℕ} (h : m=n) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).X m →ₗ[ℚ] (BinarySmallCochains.Constructions.binarySmallCochains X A B).X n := by
  subst n
  exact LinearMap.id

theorem binarySmallCochainCast_inclusion {m n : ℕ} (h : m=n)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X m) :
    BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n (binarySmallCochainCast X A B h a) =
      AlgebraicTopology.Products.Cup.cochainCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) h
        (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B m a) := by
  subst n
  rfl

theorem binarySmallRightCup_coboundary (p q : ℕ)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).d (p+q) (p+q+1) (binarySmallRightCup X A B p q a b) =
      binarySmallCochainCast X A B (by omega : (p+1)+q=p+q+1)
        (binarySmallRightCup X A B (p+1) q ((BinarySmallCochains.Constructions.binarySmallCochains X A B).d p (p+1) a) b) +
      (-1 : ℤ)^p • binarySmallRightCup X A B p (q+1) a
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1) b) := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (p+q+1)
  rw [map_add, map_zsmul, BinarySmallCochains.Constructions.binarySmallCochainInclusion_d,
    binarySmallCochainCast_inclusion, binarySmallRightCup_inclusion X A B p q,
    binarySmallRightCup_inclusion X A B (p+1) q, BinarySmallCochains.Constructions.binarySmallCochainInclusion_d]
  have hr : BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1)
      (binarySmallRightCup X A B p (q+1) a ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1) b)) =
      AlgebraicTopology.Products.Cup.singularCup X (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B p a)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1) b) :=
    binarySmallRightCup_inclusion X A B p (q+1) a _
  rw [hr]
  exact AlgebraicTopology.Products.Cup.cupWith_coboundary (TopCat.toSSet.obj X)
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ) (LinearMap.mul ℚ ℚ) _ b

theorem binarySmallRightCup_cocycle (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    binarySmallRightCup X A B p q a.val b.val ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff, binarySmallRightCup_coboundary,
    AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ a, AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ b]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]

end

/-! Multiplication by an ordinary cocycle descends to the actual small-quotient cohomology. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem cochainIncoming_zero (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) :
    (C.sc 0).f = 0 := by
  change C.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply C.shape
  change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
  omega

theorem cochainBoundary_succ_iff (C : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (n : ℕ) (x : C.X (n+1)) :
    (∃ z : (C.sc (n+1)).X₁, (C.sc (n+1)).f z = x) ↔
      ∃ z : C.X n, C.d n (n+1) z = x := by
  change (∃ z : C.X ((ComplexShape.up ℕ).prev (n+1)),
    C.d ((ComplexShape.up ℕ).prev (n+1)) (n+1) z = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

variable (X : TopCat.{0}) (A B : Set X)

theorem binarySmallBoundary_cast_iff {m n : ℕ} (h : m=n)
    (a : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X m) :
    (∃ z : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc m).X₁,
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc m).f z = a) ↔
    ∃ z : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc n).X₁,
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc n).f z = binarySmallCochainCast X A B h a := by
  subst n
  rfl

theorem binarySmallRightCup_boundary_left (p q : ℕ)
    (a : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc p).X₁)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    ∃ z : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc (p+q)).X₁,
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc (p+q)).f z =
        binarySmallRightCup X A B p q (((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc p).f a) b.val := by
  cases p with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, cochainIncoming_zero]
      change 0 = binarySmallRightCup X A B 0 q 0 b.val
      simp only [map_zero, LinearMap.zero_apply]
  | succ p =>
      obtain ⟨u,hu⟩ := (cochainBoundary_succ_iff (BinarySmallCochains.Constructions.binarySmallCochains X A B) p
        (((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc (p+1)).f a)).mp ⟨a,rfl⟩
      rw [← hu]
      apply (binarySmallBoundary_cast_iff X A B (by omega : (p+1)+q=p+q+1) _).mpr
      apply (cochainBoundary_succ_iff (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) _).mpr
      refine ⟨binarySmallRightCup X A B p q u b.val, ?_⟩
      rw [binarySmallRightCup_coboundary, AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ _ _ b]
      simp only [map_zero, smul_zero, add_zero]

def binarySmallRightCupCocycleMap (p q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) p →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) where
  toFun a := ⟨binarySmallRightCup X A B p q a.val b.val,
    binarySmallRightCup_cocycle X A B p q a b⟩
  map_add' a c := by
    apply Subtype.ext
    change binarySmallRightCup X A B p q (a.val+c.val) b.val = _
    rw [map_add, LinearMap.add_apply]
    rfl
  map_smul' r a := by
    apply Subtype.ext
    change binarySmallRightCup X A B p q (r • a.val) b.val = _
    rw [map_smul, LinearMap.smul_apply]
    rfl

theorem binarySmallRightCupCocycleMap_boundary (p q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q)
    (a : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc p).X₁) :
    binarySmallRightCupCocycleMap X A B p q b
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (BinarySmallCochains.Constructions.binarySmallCochains X A B) p a) ∈
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q) := by
  obtain ⟨z,hz⟩ := binarySmallRightCup_boundary_left X A B p q a b
  exact ⟨z, Subtype.ext hz⟩

def binarySmallRightCupClass (p q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).homology p →ₗ[ℚ] (BinarySmallCochains.Constructions.binarySmallCochains X A B).homology (p+q) :=
  ((AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (BinarySmallCochains.Constructions.binarySmallCochains X A B) p).liftQ
    ((AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q)).comp
      (binarySmallRightCupCocycleMap X A B p q b))
    (by
      rintro a ⟨u,rfl⟩
      exact (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff _ _ _).mpr
        (binarySmallRightCupCocycleMap_boundary X A B p q b u))).comp
      (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso (BinarySmallCochains.Constructions.binarySmallCochains X A B) p).toLinearEquiv.toLinearMap

theorem binarySmallRightCupClass_class (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (BinarySmallCochains.Constructions.binarySmallCochains X A B) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q) :
    binarySmallRightCupClass X A B p q b (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q) (binarySmallRightCupCocycleMap X A B p q b a) := by
  simp only [binarySmallRightCupClass, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions
