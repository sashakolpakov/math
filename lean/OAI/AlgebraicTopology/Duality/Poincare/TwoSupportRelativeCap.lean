import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Two Support Relative Cap -/

namespace OAI.AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap

noncomputable section

/-!
# The chain-level cap product with two relative supports

A rational cochain vanishing on `A` caps an integral chain modulo the
binary-small chains for `{A,B}` to a rational chain modulo `B`. The small
quotient is the native cokernel, not the full quotient by chains in `A ∪ B`.
The existing subdivision comparison identifies their homology when the
subsets are open. The construction here does not require openness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The binary-small quotient sequence is short exact in each degree. -/
theorem binarySmallComplementSequence_degreewiseShortExact
    (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementSequence X A B).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementSequence_shortExact X A B) n

/-- Every element of the actual small quotient has an ambient representative. -/
theorem binarySmallComplementProjection_surjective
    (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n) :=
  (ModuleCat.epi_iff_surjective _).mp
    (binarySmallComplementSequence_degreewiseShortExact X A B n).epi_g

/-- Its kernel is exactly the image of the binary-small chains. -/
theorem binarySmallComplementProjection_ker
    (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n).hom =
      LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f n).hom :=
  (binarySmallComplementSequence_degreewiseShortExact X A B n).exact.moduleCat_range_eq_ker.symm

private def factorThroughSurjective {R : Type} [Ring R]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    {modM : Module R M} {modN : Module R N} {modP : Module R P}
    (π : M →ₗ[R] N) (hπ : Function.Surjective π) (f : M →ₗ[R] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) : N →ₗ[R] P :=
  ((LinearMap.ker π).liftQ f hf).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

private theorem factorThroughSurjective_apply {R : Type} [Ring R]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    {modM : Module R M} {modN : Module R N} {modP : Module R P}
    (π : M →ₗ[R] N) (hπ : Function.Surjective π) (f : M →ₗ[R] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) (x : M) :
    factorThroughSurjective π hπ f hf (π x) = f x := by
  simp only [factorThroughSurjective, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Factor an integral-linear function that kills binary-small chains through
the actual cokernel in the chain category. -/
def liftBinarySmallComplementMap (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    {M : Type} [AddCommGroup M]
    (f : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hf : ∀ z, f ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f n z) = 0) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X n →ₗ[ℤ] M :=
  factorThroughSurjective ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n).hom
    (binarySmallComplementProjection_surjective X A B n) f (by
      rw [binarySmallComplementProjection_ker]
      rintro _ ⟨z, rfl⟩
      exact hf z)

@[simp]
theorem liftBinarySmallComplementMap_projection
    (X : TopCat.{0}) (A B : Set X) (n : ℕ) {M : Type} [AddCommGroup M]
    (f : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hf : ∀ z, f ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f n z) = 0)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    liftBinarySmallComplementMap X A B n f hf
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n z) = f z :=
  factorThroughSurjective_apply _ _ _ _ z

/-- Degree transport on the actual binary-small quotient. -/
def binarySmallComplementChainCast (X : TopCat.{0}) (A B : Set X)
    {m n : ℕ} (h : m = n) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X m →ₗ[ℤ]
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X n :=
  (eqToHom (congrArg (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X h)).hom

@[simp]
theorem binarySmallComplementChainCast_rfl (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    binarySmallComplementChainCast X A B (rfl : n = n) = LinearMap.id := rfl

@[simp]
theorem binarySmallComplementChainCast_symm_apply
    (X : TopCat.{0}) (A B : Set X) {m n : ℕ} (h : m = n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X m) :
    binarySmallComplementChainCast X A B h.symm
      (binarySmallComplementChainCast X A B h z) = z := by
  subst n
  rfl

@[simp]
theorem binarySmallComplementChainCast_projection
    (X : TopCat.{0}) (A B : Set X) {m n : ℕ} (h : m = n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X m) :
    binarySmallComplementChainCast X A B h
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f m z) =
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n
      (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X) h z) := by
  subst n
  rfl

@[simp]
theorem boundary_binarySmallComplementChainCast
    (X : TopCat.{0}) (A B : Set X) {m n : ℕ} (h : m = n) (j : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d n j
      (binarySmallComplementChainCast X A B h z) =
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d m j z := by
  subst n
  rfl

private theorem binarySmallChainDegreePushout (X : TopCat.{0}) (A B : Set X) (n : ℕ) :
    IsPushout
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_left : A ∩ B ⊆ A))).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion X (Set.inter_subset_right : A ∩ B ⊆ B))).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X A B)).f n)
      ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X A B)).f n) :=
  (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map_isPushout
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallChain_isPushout X A B)

/-- The projected cap of a chain lying in `B` vanishes in the relative target. -/
theorem projectedMixedCap_subspace_eq_zero
    (X : TopCat.{0}) (B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B)).X (p + q)) :
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
      (IntegralCapCoefficients.mixedSingularCap X p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X B).f (p + q) z)) = 0 := by
  rw [← IntegralCapCoefficients.mixedSingularCap_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X B) p q c z]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection ℚ X B) q) _

/-- A cochain vanishing on `A` kills all `{A,B}`-small chains after projecting
the cap result modulo `B`. This uses the genuine pushout of small chains. -/
theorem projectedMixedCap_binarySmall_eq_zero
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X A B).X (p + q)) :
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
      (IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q) z)) = 0 := by
  let F : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X A B).X (p + q) ⟶
      ModuleCat.of ℤ ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X q) :=
    ModuleCat.ofHom
      ((((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q).hom.restrictScalars ℤ).comp
        ((IntegralCapCoefficients.mixedSingularCap X p q
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)).comp
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q)).hom))
  have hF : F = 0 := by
    apply (binarySmallChainDegreePushout X A B (p + q)).hom_ext
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
        (IntegralCapCoefficients.mixedSingularCap X p q
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q)
            ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map
              (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X A B)).f (p + q) w))) = 0
      have hw := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
        (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left X A B) (p + q)) w
      change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularLeft X A B)).f (p + q) w) =
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) w at hw
      rw [hw, SupportRelativeCap.relativeCochain_cap_subspace_eq_zero, map_zero]
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
        (IntegralCapCoefficients.mixedSingularCap X p q
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
          ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q)
            ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map
              (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X A B)).f (p + q) w))) = 0
      have hw := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
        (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X A B) (p + q)) w
      change (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularRight X A B)).f (p + q) w) =
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X B).f (p + q) w at hw
      rw [hw]
      exact projectedMixedCap_subspace_eq_zero X B p q _ w
  exact ConcreteCategory.congr_hom hF z

private def twoSupportSmallCapForCochain (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X (p + q) →ₗ[ℤ]
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X q :=
  liftBinarySmallComplementMap X A B (p + q)
    ((((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q).hom.restrictScalars ℤ).comp
      (IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)))
    (projectedMixedCap_binarySmall_eq_zero X A B p q c)

private theorem twoSupportSmallCapForCochain_projection
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    twoSupportSmallCapForCochain X A B p q c
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
      (IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z) :=
  liftBinarySmallComplementMap_projection _ _ _ _ _ _ z

/-- The actual mixed cap with two relative supports. Its source is the
small-chain cokernel and its target is rational chains relative to `B`. -/
def twoSupportSmallCap (X : TopCat.{0}) (A B : Set X) (p q : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p →ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X (p + q) →ₗ[ℤ]
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X q) where
  toFun := twoSupportSmallCapForCochain X A B p q
  map_add' c d := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := binarySmallComplementProjection_surjective X A B (p + q) z
    simp only [twoSupportSmallCapForCochain_projection, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := binarySmallComplementProjection_surjective X A B (p + q) z
    simp only [twoSupportSmallCapForCochain_projection, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- Evaluation on an ambient representative is exactly the projected finite
Alexander--Whitney cap. -/
@[simp]
theorem twoSupportSmallCap_projection
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    twoSupportSmallCap X A B p q c
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
      (IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z) :=
  twoSupportSmallCapForCochain_projection X A B p q c z

/-- Compatibility with the existing one-support cap, followed by the actual
rational relative projection. -/
theorem twoSupportSmallCap_left
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q)) :
    twoSupportSmallCap X A B p q c
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B).f (p + q) z) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q (SupportRelativeCap.relativeCap X A p q c z) := by
  obtain ⟨z, rfl⟩ := SupportRelativeCap.relativeChainProjection_surjective X A (p + q) z
  have hz := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection X A B) (p + q)) z
  change (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B).f (p + q)
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q) z) =
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q) z at hz
  rw [hz, twoSupportSmallCap_projection, SupportRelativeCap.relativeCap_projection]

/-- The exact signed cap boundary identity in the two relative quotients. -/
theorem twoSupportSmallCap_boundary
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X (p + q + 1)) :
    twoSupportSmallCap X A B p q c
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d (p + q + 1) (p + q) z) =
      twoSupportSmallCap X A B (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (binarySmallComplementChainCast X A B (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q
        (twoSupportSmallCap X A B p (q + 1) c z)) := by
  obtain ⟨z, rfl⟩ := binarySmallComplementProjection_surjective X A B (p + q + 1) z
  have hπ := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).comm (p + q + 1) (p + q)) z
  have hι := ConcreteCategory.congr_hom
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).comm p (p + 1)) c
  change (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d (p + q + 1) (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) at hπ
  change (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) =
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c) at hι
  rw [hπ, binarySmallComplementChainCast_projection,
    twoSupportSmallCap_projection, twoSupportSmallCap_projection]
  erw [twoSupportSmallCap_projection X A B p (q + 1) c z]
  rw [← hι]
  have htarget := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).comm (q + 1) q)
    (IntegralCapCoefficients.mixedSingularCap X p (q + 1)
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z)
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q
      ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f (q + 1)
        (IntegralCapCoefficients.mixedSingularCap X p (q + 1)
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z)) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
        (IntegralCapCoefficients.mixedSingularCap X p (q + 1)
          ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z)) at htarget
  rw [htarget]
  have h := congrArg ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f q)
    (IntegralCapCoefficients.mixedSingularCap_boundary X p q
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z)
  simpa only [map_add, map_zsmul] using h

/-- The signed identity solved for the boundary of the relative output. -/
theorem boundary_twoSupportSmallCap
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X (p + q + 1)) :
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q
        (twoSupportSmallCap X A B p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (twoSupportSmallCap X A B p q c
            ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d (p + q + 1) (p + q) z) -
          twoSupportSmallCap X A B (p + 1) q
            ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
            (binarySmallComplementChainCast X A B
              (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [twoSupportSmallCap_boundary, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

end

end OAI.AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap
