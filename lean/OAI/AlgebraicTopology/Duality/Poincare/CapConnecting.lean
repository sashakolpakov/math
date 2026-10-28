import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
import OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives
import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

/-! # Cap Connecting -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapConnecting

noncomputable section

/-!
# Cap products and connecting representatives

The signs here come from the proved front-face cap boundary formula. Actual
cochain and chain lifts give explicit boundaries witnessing compatibility;
the subsequent class identities use the native connecting homomorphisms.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- Capping the coboundary of a lifted cochain agrees, up to the displayed
signed boundary, with capping its restriction against the lifted boundary. -/
theorem mixedCap_pair_lift_boundary (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q + 1))
    (v : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q))
    (hv : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) v =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) :
    IntegralCapCoefficients.mixedSingularCap X (p + 1) q
        ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) b)
        (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X)
          (by omega : p + q + 1 = (p + 1) + q) z) =
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f q
        (IntegralCapCoefficients.mixedSingularCap (TopCat.of A) p q
          ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X A).f p b) v) -
      ((-1 : ℤ) ^ p) • (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q
        (IntegralCapCoefficients.mixedSingularCap X p (q + 1) b z) := by
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = IntegralCapCoefficients.mixedSingularCap X p q b
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) :=
      (IntegralCapCoefficients.mixedSingularCap_boundary X p q b z).symm
    _ = IntegralCapCoefficients.mixedSingularCap X p q b ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) v) := by
      rw [← hv]
    _ = _ := (IntegralCapCoefficients.mixedSingularCap_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) p q b v).symm

/-- The difference in the pair compatibility formula is an explicit
boundary, with no cocycle or global duality hypothesis. -/
theorem mixedCap_pair_lift_difference (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q + 1))
    (v : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q))
    (hv : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) v =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q
        (- (((-1 : ℤ) ^ p) • IntegralCapCoefficients.mixedSingularCap X p (q + 1) b z)) =
      IntegralCapCoefficients.mixedSingularCap X (p + 1) q
        ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) b)
        (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X)
          (by omega : p + q + 1 = (p + 1) + q) z) -
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f q
        (IntegralCapCoefficients.mixedSingularCap (TopCat.of A) p q
          ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of R R) X A).f p b) v) := by
  rw [map_neg, map_zsmul, mixedCap_pair_lift_boundary X A p q b z v hv]
  abel

/-- The same explicit boundary identity for the actual support-relative
cap product, evaluated on a pair of representatives. -/
theorem relativeCap_pair_lift_difference (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (b : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X (p + 1))
    (hc : (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1) c =
      (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p (p + 1) b)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q + 1))
    (v : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q))
    (hv : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) v =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
        (- (((-1 : ℤ) ^ p) • IntegralCapCoefficients.mixedSingularCap X p (q + 1) b z)) =
      SupportRelativeCap.relativeCap X A (p + 1) q c
        (SupportRelativeCap.relativeChainCast X A (by omega : p + q + 1 = (p + 1) + q)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q + 1) z)) -
      (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f q
        (IntegralCapCoefficients.mixedSingularCap (TopCat.of A) p q
          ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f p b) v) := by
  rw [SupportRelativeCap.relativeChainCast_projection]
  erw [SupportRelativeCap.relativeCap_projection, hc]
  exact mixedCap_pair_lift_difference X A p q b z v hv

/-- For a relative cycle, capping turns the cochain differential into the
chain differential with the sign needed in a connecting-map square. -/
theorem relativeCap_boundary_cycle (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
        (SupportRelativeCap.relativeCap X A p (q + 1) c z.val) =
      ((-1 : ℤ) ^ (p + 1)) • SupportRelativeCap.relativeCap X A (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (SupportRelativeCap.relativeChainCast X A (by omega : p + q + 1 = (p + 1) + q) z.val) := by
  rw [SupportRelativeCap.boundary_relativeCap,
    Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q + 1) (p + q) z,
    map_zero, zero_sub, pow_succ, mul_smul, neg_one_smul]

/-- Transporting a native homology class along equality of its degree
transports its actual cycle representative. -/
theorem homologyDegreeCast_chainClass
    (C : ChainComplex (ModuleCat.{0} R) ℕ) {m n : ℕ} (h : m = n)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles C m) :
    (eqToHom (congrArg (fun k => C.homology k) h)) (Cohomology.Singular.ChainRepresentatives.chainClass C m z) =
      Cohomology.Singular.ChainRepresentatives.chainClass C n (h ▸ z) := by
  subst n
  rfl

/-- Degree transport of a relative cycle agrees with transport of its
underlying relative chain. -/
theorem relativeCycleDegreeCast_val (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) m) :
    ((h ▸ z) : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n).val =
      SupportRelativeCap.relativeChainCast X A h z.val := by
  subst n
  rfl

/-- Pair connecting compatibility for the actual support-relative cap
product. The explicit signed boundary above vanishes on homology, leaving
the usual identity between the two native connecting homomorphisms. -/
theorem relativeCapHomology_connecting (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of A) p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q + 1)) :
    SupportRelativeCap.relativeCapHomology X A (p + 1) q
        (Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A p a)
        ((eqToHom (congrArg (fun k => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).homology k)
          (by omega : p + q + 1 = (p + 1) + q))) z) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) q
        (MixedCapHomology.mixedSingularCapHomology (TopCat.of A) p q a
          (AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary X A (p + q) z)) := by
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (TopCat.of A) p a
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q + 1) z
  obtain ⟨b, c, hb, hc, hδc⟩ := ConnectingRepresentatives.cohomologyConnecting_representatives_exist
    (Cohomology.Singular.RelativeSequence.relativeCochainSequence (ModuleCat.of ℚ ℚ) X A)
    (Cohomology.Singular.RelativeSequence.relativeCochainSequence_shortExact (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨w, v, hw, hv, hδz⟩ := ConnectingRepresentatives.homologyConnecting_representatives_exist
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence X A) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_shortExact X A) (p + q) z
  change (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f p b = a.val at hb
  change (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1) c.val =
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p (p + 1) b at hc
  change Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A p
      (Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (TopCat.of A) p a) =
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (p + 1) c at hδc
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q + 1) w = z.val at hw
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) v.val =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) w at hv
  change AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary X A (p + q)
      (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q + 1) z) =
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)) (p + q) v at hδz
  rw [hδc, hδz, homologyDegreeCast_chainClass,
    SupportRelativeCap.relativeCapHomology_class_class, MixedCapHomology.mixedSingularCapHomology_class_class]
  simp only [Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward, Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_iff_exists (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q _ _).mpr
  refine ⟨- (((-1 : ℤ) ^ p) • IntegralCapCoefficients.mixedSingularCap X p (q + 1) b w), ?_⟩
  let hdeg : p + q + 1 = (p + 1) + q := by omega
  have hzval : ((hdeg ▸ z) : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) ((p + 1) + q)).val =
      SupportRelativeCap.relativeChainCast X A hdeg ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q + 1) w) := by
    rw [hw]
    exact relativeCycleDegreeCast_val X A hdeg z
  have hcap := relativeCap_pair_lift_difference X A p q b c.val hc w v.val hv
  rw [hb, ← hzval] at hcap
  exact hcap

end

end OAI.AlgebraicTopology.Duality.Poincare.CapConnecting
