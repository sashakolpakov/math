import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Support Relative Cap -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap

noncomputable section

/-!
# Finite cap products for relative support

A rational cochain in the actual kernel of restriction to a subspace caps
an integral chain modulo that subspace to an ordinary rational chain. The
construction uses the genuine relative quotient; no representative or
support hypothesis is added to the resulting pairing. Its signed boundary
identity descends the pairing to the existing categorical (co)homology.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence OAI.AlgebraicTopology.Products.CapBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual integral relative chain has an ordinary finite representative. -/
theorem relativeChainProjection_surjective (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n) :=
  (ModuleCat.epi_iff_surjective _).1
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X A n).epi_g

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

private def integralLinearMapOfAddHom {M N : Type}
    [AddCommGroup M] [AddCommGroup N]
    {modM : Module ℤ M} {modN : Module ℤ N} (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (modM.smul r x) = modN.smul r (f x)
    simp only [int_smul_eq_zsmul, map_zsmul]

/-- Factor a linear function on ordinary chains through the actual relative
quotient when it vanishes on the subspace-chain image. -/
def liftRelativeChainMap (X : TopCat.{0}) (A : Set X) (n : ℕ)
    {M : Type} [AddCommGroup M]
    (f : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hf : ∀ z, f ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n z) = 0) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n →ₗ[ℤ] M :=
  factorThroughSurjective ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom
    (relativeChainProjection_surjective X A n) f (by
    have hk : LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom =
        LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom :=
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainSequence_degreewiseShortExact X A n).exact.moduleCat_range_eq_ker
    rw [← hk]
    rintro _ ⟨z, rfl⟩
    exact hf z)

@[simp]
theorem liftRelativeChainMap_projection (X : TopCat.{0}) (A : Set X) (n : ℕ)
    {M : Type} [AddCommGroup M]
    (f : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hf : ∀ z, f ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n z) = 0)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    liftRelativeChainMap X A n f hf ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z) = f z := by
  exact factorThroughSurjective_apply _ _ _ _ z

/-- Transport the actual relative chain module along an equality of degrees. -/
def relativeChainCast (X : TopCat.{0}) (A : Set X) {m n : ℕ} (h : m = n) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X m →ₗ[ℤ] (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n :=
  (eqToHom (congrArg (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X h)).hom

@[simp]
theorem relativeChainCast_rfl (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeChainCast X A (rfl : n = n) = LinearMap.id := rfl

@[simp]
theorem relativeChainCast_symm_apply (X : TopCat.{0}) (A : Set X) {m n : ℕ}
    (h : m = n) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X m) :
    relativeChainCast X A h.symm (relativeChainCast X A h z) = z := by
  subst n
  rfl

@[simp]
theorem relativeChainCast_projection (X : TopCat.{0}) (A : Set X) {m n : ℕ}
    (h : m = n) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X m) :
    relativeChainCast X A h ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f m z) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n
        (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X) h z) := by
  subst n
  rfl

@[simp]
theorem boundary_relativeChainCast (X : TopCat.{0}) (A : Set X) {m n : ℕ}
    (h : m = n) (j : ℕ) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X m) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d n j (relativeChainCast X A h z) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d m j z := by
  subst n
  rfl

/-- Relative cochains vanish on the actual restriction to the subspace. -/
theorem relativeCochain_restriction_eq_zero (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f p
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) = 0 :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction (ModuleCat.of ℚ ℚ) X A) p) c

/-- A relative cochain annihilates every cap input coming from the subspace. -/
theorem relativeCochain_cap_subspace_eq_zero (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)).X (p + q)) :
    IntegralCapCoefficients.mixedSingularCap X p q
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f (p + q) z) = 0 := by
  have h := IntegralCapCoefficients.mixedSingularCap_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z
  have hc := relativeCochain_restriction_eq_zero X A p c
  change (Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f p
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) = 0 at hc
  simpa only [hc, map_zero, LinearMap.zero_apply] using h.symm

private def relativeCapForCochain (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q) →ₗ[ℤ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X q :=
  liftRelativeChainMap X A (p + q)
    (IntegralCapCoefficients.mixedSingularCap X p q ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c))
    (relativeCochain_cap_subspace_eq_zero X A p q c)

private theorem relativeCapForCochain_projection (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    relativeCapForCochain X A p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q) z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z :=
  liftRelativeChainMap_projection _ _ _ _ _ z

/-- Genuine finite support-relative cap product, rational in the cochain and
integral-linear in the relative chain. Its output is an ordinary rational chain. -/
def relativeCap (X : TopCat.{0}) (A : Set X) (p q : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p →ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q) →ₗ[ℤ]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X q) where
  toFun := relativeCapForCochain X A p q
  map_add' c d := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := relativeChainProjection_surjective X A (p + q) z
    simp only [relativeCapForCochain_projection, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := relativeChainProjection_surjective X A (p + q) z
    simp only [relativeCapForCochain_projection, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- Evaluation on an ordinary representative is exactly the previously
constructed mixed cap product. -/
@[simp]
theorem relativeCap_projection (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    relativeCap X A p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q) z) =
      IntegralCapCoefficients.mixedSingularCap X p q
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z :=
  relativeCapForCochain_projection X A p q c z

/-- The signed boundary formula survives the relative quotient exactly. -/
theorem relativeCap_boundary (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q + 1)) :
    relativeCap X A p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (p + q + 1) (p + q) z) =
      relativeCap X A (p + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
        (relativeChainCast X A (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
        (relativeCap X A p (q + 1) c z)) := by
  obtain ⟨z, rfl⟩ := relativeChainProjection_surjective X A (p + q + 1) z
  have hπ := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm (p + q + 1) (p + q)) z
  have hι := ConcreteCategory.congr_hom
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).comm p (p + 1)) c
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (p + q + 1) (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q + 1) z) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) at hπ
  change (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d p (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) =
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (p + 1)
      ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c) at hι
  rw [hπ, relativeChainCast_projection, relativeCap_projection, relativeCap_projection]
  erw [relativeCap_projection X A p (q + 1) c z]
  rw [← hι]
  exact IntegralCapCoefficients.mixedSingularCap_boundary X p q
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z

/-- The relative boundary formula solved for the ordinary output boundary. -/
theorem boundary_relativeCap (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
        (relativeCap X A p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (relativeCap X A p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (p + q + 1) (p + q) z) -
          relativeCap X A (p + 1) q
            ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d p (p + 1) c)
            (relativeChainCast X A (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [relativeCap_boundary, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

/-- A relative cocycle caps a relative cycle to an ordinary rational cycle,
also in output degree zero. -/
theorem relativeCap_mem_chainCycles (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    relativeCap X A p q c.val z.val ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q := by
  cases q with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ q =>
    apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q _).mpr
    rw [boundary_relativeCap X A p q c.val z.val]
    have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)
      (p + q + 1) (p + q) z
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
      p (p + 1) c
    simp only [hz, hc, map_zero, LinearMap.zero_apply, sub_self, smul_zero]

/-- The finite relative cap pairing restricted to actual cycles. -/
def relativeCapCycles (X : TopCat.{0}) (A : Set X) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p →ₗ[ℚ]
      (Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) →ₗ[ℤ]
        Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q) where
  toFun c := integralLinearMapOfAddHom {
    toFun := fun z => ⟨relativeCap X A p q c.val z.val,
      relativeCap_mem_chainCycles X A p q c z⟩
    map_zero' := by
      apply Subtype.ext
      exact (relativeCap X A p q c.val).map_zero
    map_add' := by
      intro z w
      apply Subtype.ext
      exact (relativeCap X A p q c.val).map_add z.val w.val }
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change relativeCap X A p q (c.val + d.val) z.val =
      relativeCap X A p q c.val z.val + relativeCap X A p q d.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change relativeCap X A p q (r • c.val) z.val = r • relativeCap X A p q c.val z.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem relativeCapCycles_val (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    (relativeCapCycles X A p q c z).val = relativeCap X A p q c.val z.val := rfl

/-- A relative chain boundary capped with a relative cocycle is an ordinary
rational boundary, with an explicit finite-chain witness. -/
theorem relativeCap_cocycle_boundary_exists (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (i : ℕ) (w : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X i) :
    ∃ v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X (q + 1),
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q v =
        relativeCap X A p q c.val ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d i (p + q) w) := by
  by_cases hi : (ComplexShape.down ℕ).Rel i (p + q)
  · have hi' : p + q + 1 = i := hi
    subst i
    refine ⟨((-1 : ℤ) ^ p) • relativeCap X A p (q + 1) c.val w, ?_⟩
    have h := relativeCap_boundary X A p q c.val w
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
      p (p + 1) c
    simpa only [hc, map_zero, LinearMap.zero_apply, zero_add, map_zsmul] using h.symm
  · refine ⟨0, ?_⟩
    rw [(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).shape i (p + q) hi]
    simp

/-- A relative coboundary capped with a relative cycle is an ordinary
rational boundary. Off-shape incoming differentials include degree zero. -/
theorem relativeCap_coboundary_cycle_exists (X : TopCat.{0}) (A : Set X) (i p q : ℕ)
    (a : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X i)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    ∃ v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X (q + 1),
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q v =
        relativeCap X A p q ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i p a)
          z.val := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · have hp : i + 1 = p := hip
    subst p
    have hdeg : (i + 1) + q = i + q + 1 := by omega
    let w := relativeChainCast X A hdeg z.val
    have hw : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (i + q + 1) (i + q) w = 0 := by
      change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d (i + q + 1) (i + q)
        (relativeChainCast X A hdeg z.val) = 0
      rw [boundary_relativeChainCast]
      exact Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) ((i + 1) + q) (i + q) z
    have hb : relativeChainCast X A (by omega : i + q + 1 = (i + 1) + q) w = z.val :=
      relativeChainCast_symm_apply X A hdeg z.val
    have h := relativeCap_boundary X A i q a w
    rw [hw, map_zero, hb] at h
    refine ⟨- (((-1 : ℤ) ^ i) • relativeCap X A i (q + 1) a w), ?_⟩
    have heq : relativeCap X A (i + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i (i + 1) a) z.val =
        - (((-1 : ℤ) ^ i) • (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q
          (relativeCap X A i (q + 1) a w)) :=
      eq_neg_of_add_eq_zero_left h.symm
    simpa only [map_neg, map_zsmul] using heq.symm
  · refine ⟨0, ?_⟩
    rw [(Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).shape i p hip]
    simp

/-- A fixed relative cocycle acts on the genuine relative integral homology. -/
def relativeCapCocycleHomology (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q) →ₗ[ℤ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q :=
  factorThroughSurjective (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q))
    (Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q))
    (integralLinearMapOfAddHom
      ((Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q).toAddMonoidHom.comp
        (relativeCapCycles X A p q c).toAddMonoidHom))
    (by
      intro z hz
      rcases (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z).mp hz with
        ⟨w, rfl⟩
      change Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q
        (relativeCapCycles X A p q c
          (Cohomology.Singular.ChainRepresentatives.chainBoundaryMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) w)) = 0
      apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q _).mpr
      change ∃ v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X (q + 1),
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q v =
          relativeCap X A p q c.val (((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).sc (p + q)).f w)
      exact relativeCap_cocycle_boundary_exists X A p q c _ w)

@[simp]
theorem relativeCapCocycleHomology_chainClass (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    relativeCapCocycleHomology X A p q c
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q (relativeCapCycles X A p q c z) := by
  dsimp only [relativeCapCocycleHomology]
  rw [factorThroughSurjective_apply]
  rfl

/-- The action on relative homology is rational-linear in the relative cocycle. -/
def relativeCocycleCapHomology (X : TopCat.{0}) (A : Set X) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p →ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q) →ₗ[ℤ]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q) where
  toFun := relativeCapCocycleHomology X A p q
  map_add' c d := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) h
    simp only [relativeCapCocycleHomology_chainClass, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) h
    simp only [relativeCapCocycleHomology_chainClass, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- Relative coboundaries act by zero on relative homology. -/
@[simp]
theorem relativeCocycleCapHomology_boundary (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (a : ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).sc p).X₁) :
    relativeCocycleCapHomology X A p q
      (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) h
  change relativeCapCocycleHomology X A p q
    (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a)
    (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z) = 0
  rw [relativeCapCocycleHomology_chainClass]
  apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q _).mpr
  change ∃ v : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X (q + 1),
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 1) q v =
      relativeCap X A p q (((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).sc p).f a)
        z.val
  exact relativeCap_coboundary_cycle_exists X A _ p q a z

/-- The actual support-relative pairing on rational cohomology and integral
homology, taking values in ordinary rational homology. -/
def relativeCapHomology (X : TopCat.{0}) (A : Set X) (p q : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q) →ₗ[ℤ]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q) :=
  ((Cohomology.Singular.Representatives.cochainBoundaries (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p).liftQ
    (relativeCocycleCapHomology X A p q)
    (by
      intro c hc
      rcases hc with ⟨a, rfl⟩
      exact relativeCocycleCapHomology_boundary X A p q a)).comp
    (Cohomology.Singular.Representatives.cohomologyQuotientIso (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p).toLinearEquiv.toLinearMap

/-- On represented classes the descended pairing is precisely the ordinary
class of the finite relative cap cycle. -/
@[simp]
theorem relativeCapHomology_class_class (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q)) :
    relativeCapHomology X A p q
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q (relativeCapCycles X A p q c z) := by
  dsimp only [relativeCapHomology, Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact relativeCapCocycleHomology_chainClass X A p q c z

/-- Both inputs may be changed by actual (co)boundaries without changing the
ordinary output homology class. -/
theorem relativeCapHomology_independent (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (c c' : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z z' : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q))
    (hc : Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c')
    (hz : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z') :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q (relativeCapCycles X A p q c z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) q (relativeCapCycles X A p q c' z') := by
  rw [← relativeCapHomology_class_class, ← relativeCapHomology_class_class, hc, hz]

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
