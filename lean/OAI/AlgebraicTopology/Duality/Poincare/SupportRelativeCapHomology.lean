import OAI.AlgebraicTopology.Duality.Poincare.TwoSupportRelativeCap
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Support Relative Cap Homology -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology

noncomputable section

/-!
# Cap on actual relative cohomology and homology with two supports

The signed chain identity proves that cocycles cap cycles to relative
cycles and that both kinds of boundaries map to boundaries. Descending
first through the actual small-chain quotient homology and then through
cohomology gives a bilinear pairing. For open support sets, the verified
subdivision comparison transports this pairing to the standard relative
homology of their union.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- A relative cocycle caps a small-quotient cycle to a relative rational cycle,
also in output degree zero. -/
theorem twoSupportSmallCap_mem_chainCycles (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val z.val ∈ Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q := by
  cases q with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ q =>
    apply (Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q _).mpr
    rw [TwoSupportRelativeCap.boundary_twoSupportSmallCap X A B p q c.val z.val]
    have hz := Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B)
      (p + q + 1) (p + q) z
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
      p (p + 1) c
    simp only [hz, hc, map_zero, LinearMap.zero_apply, sub_self, smul_zero]

/-- The finite relative cap pairing restricted to actual cycles. -/
def twoSupportSmallCapCycles (X : TopCat.{0}) (A B : Set X) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p →ₗ[ℚ]
      (Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) →ₗ[ℤ]
        Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q) where
  toFun c := integralLinearMapOfAddHom {
    toFun := fun z => ⟨TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val z.val,
      twoSupportSmallCap_mem_chainCycles X A B p q c z⟩
    map_zero' := by
      apply Subtype.ext
      exact (TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val).map_zero
    map_add' := by
      intro z w
      apply Subtype.ext
      exact (TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val).map_add z.val w.val }
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change TwoSupportRelativeCap.twoSupportSmallCap X A B p q (c.val + d.val) z.val =
      TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val z.val + TwoSupportRelativeCap.twoSupportSmallCap X A B p q d.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change TwoSupportRelativeCap.twoSupportSmallCap X A B p q (r • c.val) z.val = r • TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val z.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem twoSupportSmallCapCycles_val (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    (twoSupportSmallCapCycles X A B p q c z).val = TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val z.val := rfl

/-- A small-quotient chain boundary capped with a relative cocycle is a relative
rational boundary, with an explicit finite-chain witness. -/
theorem twoSupportSmallCap_cocycle_boundary_exists (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (i : ℕ) (w : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X i) :
    ∃ v : (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X (q + 1),
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q v =
        TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d i (p + q) w) := by
  by_cases hi : (ComplexShape.down ℕ).Rel i (p + q)
  · have hi' : p + q + 1 = i := hi
    subst i
    refine ⟨((-1 : ℤ) ^ p) • TwoSupportRelativeCap.twoSupportSmallCap X A B p (q + 1) c.val w, ?_⟩
    have h := TwoSupportRelativeCap.twoSupportSmallCap_boundary X A B p q c.val w
    have hc := Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)
      p (p + 1) c
    simpa only [hc, map_zero, LinearMap.zero_apply, zero_add, map_zsmul] using h.symm
  · refine ⟨0, ?_⟩
    rw [(AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).shape i (p + q) hi]
    simp

/-- A relative coboundary capped with a small-quotient cycle is a relative
rational boundary. Off-shape incoming differentials include degree zero. -/
theorem twoSupportSmallCap_coboundary_cycle_exists (X : TopCat.{0}) (A B : Set X) (i p q : ℕ)
    (a : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X i)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    ∃ v : (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X (q + 1),
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q v =
        TwoSupportRelativeCap.twoSupportSmallCap X A B p q ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i p a)
          z.val := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · have hp : i + 1 = p := hip
    subst p
    have hdeg : (i + 1) + q = i + q + 1 := by omega
    let w := TwoSupportRelativeCap.binarySmallComplementChainCast X A B hdeg z.val
    have hw : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d (i + q + 1) (i + q) w = 0 := by
      change (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d (i + q + 1) (i + q)
        (TwoSupportRelativeCap.binarySmallComplementChainCast X A B hdeg z.val) = 0
      rw [TwoSupportRelativeCap.boundary_binarySmallComplementChainCast]
      exact Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) ((i + 1) + q) (i + q) z
    have hb : TwoSupportRelativeCap.binarySmallComplementChainCast X A B (by omega : i + q + 1 = (i + 1) + q) w = z.val :=
      TwoSupportRelativeCap.binarySmallComplementChainCast_symm_apply X A B hdeg z.val
    have h := TwoSupportRelativeCap.twoSupportSmallCap_boundary X A B i q a w
    rw [hw, map_zero, hb] at h
    refine ⟨- (((-1 : ℤ) ^ i) • TwoSupportRelativeCap.twoSupportSmallCap X A B i (q + 1) a w), ?_⟩
    have heq : TwoSupportRelativeCap.twoSupportSmallCap X A B (i + 1) q
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i (i + 1) a) z.val =
        - (((-1 : ℤ) ^ i) • (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q
          (TwoSupportRelativeCap.twoSupportSmallCap X A B i (q + 1) a w)) :=
      eq_neg_of_add_eq_zero_left h.symm
    simpa only [map_neg, map_zsmul] using heq.symm
  · refine ⟨0, ?_⟩
    rw [(Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).shape i p hip]
    simp

/-- A fixed relative cocycle acts on the actual small-quotient integral homology. -/
def twoSupportSmallCapCocycleHomology (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology (p + q) →ₗ[ℤ]
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).homology q :=
  factorThroughSurjective (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q))
    (Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q))
    (integralLinearMapOfAddHom
      ((Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q).toAddMonoidHom.comp
        (twoSupportSmallCapCycles X A B p q c).toAddMonoidHom))
    (by
      intro z hz
      rcases (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z).mp hz with
        ⟨w, rfl⟩
      change Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q
        (twoSupportSmallCapCycles X A B p q c
          (Cohomology.Singular.ChainRepresentatives.chainBoundaryMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) w)) = 0
      apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q _).mpr
      change ∃ v : (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X (q + 1),
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q v =
          TwoSupportRelativeCap.twoSupportSmallCap X A B p q c.val (((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).sc (p + q)).f w)
      exact twoSupportSmallCap_cocycle_boundary_exists X A B p q c _ w)

@[simp]
theorem twoSupportSmallCapCocycleHomology_chainClass (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    twoSupportSmallCapCocycleHomology X A B p q c
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q (twoSupportSmallCapCycles X A B p q c z) := by
  dsimp only [twoSupportSmallCapCocycleHomology]
  rw [factorThroughSurjective_apply]
  rfl

/-- The action on relative homology is rational-linear in the relative cocycle. -/
def twoSupportSmallCocycleCapHomology (X : TopCat.{0}) (A B : Set X) (p q : ℕ) :
    Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p →ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology (p + q) →ₗ[ℤ]
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).homology q) where
  toFun := twoSupportSmallCapCocycleHomology X A B p q
  map_add' c d := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) h
    simp only [twoSupportSmallCapCocycleHomology_chainClass, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) h
    simp only [twoSupportSmallCapCocycleHomology_chainClass, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- Relative coboundaries act by zero on relative homology. -/
@[simp]
theorem twoSupportSmallCocycleCapHomology_boundary (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (a : ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).sc p).X₁) :
    twoSupportSmallCocycleCapHomology X A B p q
      (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) h
  change twoSupportSmallCapCocycleHomology X A B p q
    (Cohomology.Singular.Representatives.cochainBoundaryMap (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a)
    (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z) = 0
  rw [twoSupportSmallCapCocycleHomology_chainClass]
  apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q _).mpr
  change ∃ v : (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).X (q + 1),
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).d (q + 1) q v =
      TwoSupportRelativeCap.twoSupportSmallCap X A B p q (((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).sc p).f a)
        z.val
  exact twoSupportSmallCap_coboundary_cycle_exists X A B _ p q a z

/-- The pairing on actual rational cohomology and integral homology of the
small-chain quotient, taking values in rational homology relative to `B`. -/
def twoSupportSmallCapHomology (X : TopCat.{0}) (A B : Set X) (p q : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology (p + q) →ₗ[ℤ]
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B).homology q) :=
  ((Cohomology.Singular.Representatives.cochainBoundaries (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p).liftQ
    (twoSupportSmallCocycleCapHomology X A B p q)
    (by
      intro c hc
      rcases hc with ⟨a, rfl⟩
      exact twoSupportSmallCocycleCapHomology_boundary X A B p q a)).comp
    (Cohomology.Singular.Representatives.cohomologyQuotientIso (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p).toLinearEquiv.toLinearMap

/-- On represented classes the descended pairing is precisely the relative
class of the finite relative cap cycle. -/
@[simp]
theorem twoSupportSmallCapHomology_class_class (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    twoSupportSmallCapHomology X A B p q
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q (twoSupportSmallCapCycles X A B p q c z) := by
  dsimp only [twoSupportSmallCapHomology, Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact twoSupportSmallCapCocycleHomology_chainClass X A B p q c z

/-- Both inputs may be changed by actual (co)boundaries without changing the
relative output homology class. -/
theorem twoSupportSmallCapHomology_independent (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c c' : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z z' : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q))
    (hc : Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c')
    (hz : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z') :
    Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q (twoSupportSmallCapCycles X A B p q c z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q (twoSupportSmallCapCycles X A B p q c' z') := by
  rw [← twoSupportSmallCapHomology_class_class, ← twoSupportSmallCapHomology_class_class, hc, hz]

/-- The small pairing on the image of a one-support class is exactly the
old cap pairing followed by the genuine relative rational projection. -/
theorem twoSupportSmallCapHomology_left
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    twoSupportSmallCapHomology X A B p q c
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B) (p + q) z) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B) q
        (SupportRelativeCap.relativeCapHomology X A p q c z) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) (p + q) z
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, twoSupportSmallCapHomology_class_class,
    SupportRelativeCap.relativeCapHomology_class_class, Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  congr 1
  apply Subtype.ext
  exact TwoSupportRelativeCap.twoSupportSmallCap_left X A B p q c.val z.val

/-- The genuine two-support relative cap product. Openness is used only for
the proved subdivision comparison with the standard relative chain quotient. -/
def twoSupportRelativeCapHomology
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (p + q) →ₗ[ℤ]
        AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X B q) where
  toFun c := (twoSupportSmallCapHomology X A B p q c).comp
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).inv.hom
  map_add' c d := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Exact evaluation of the standard relative cap through the inverse of
the actual small-chain homology comparison. -/
theorem twoSupportRelativeCapHomology_apply
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (p + q)) :
    twoSupportRelativeCapHomology X A B hA hB p q c z =
      twoSupportSmallCapHomology X A B p q c
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).inv z) := rfl

/-- On the image of an actual small-quotient homology class, the standard
relative pairing is the already descended small pairing. -/
@[simp]
theorem twoSupportRelativeCapHomology_comparison
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).homology (p + q)) :
    twoSupportRelativeCapHomology X A B hA hB p q c
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom z) =
      twoSupportSmallCapHomology X A B p q c z := by
  rw [twoSupportRelativeCapHomology_apply]
  change twoSupportSmallCapHomology X A B p q c
    (((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom ≫
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).inv) z) = _
  rw [Iso.hom_inv_id]
  rfl

/-- The standard relative cap on represented classes is exactly the
relative rational class of the explicit finite cap cycle. -/
@[simp]
theorem twoSupportRelativeCapHomology_class_class
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q)) :
    twoSupportRelativeCapHomology X A B hA hB p q
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c)
        ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom
          (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B) (p + q) z)) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) q (twoSupportSmallCapCycles X A B p q c z) := by
  rw [twoSupportRelativeCapHomology_comparison, twoSupportSmallCapHomology_class_class]

/-- Compatibility with the genuine one-support pairing after enlarging
the relative input subspace and projecting the rational output modulo `B`. -/
theorem twoSupportRelativeCapHomology_left
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    twoSupportRelativeCapHomology X A B hA hB p q c
        (HomologicalComplex.homologyMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B)) (p + q) z) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B) q
        (SupportRelativeCap.relativeCapHomology X A p q c z) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyMap_comp (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B) (p + q)) z
  rw [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_toRelative] at h
  rw [h]
  change twoSupportRelativeCapHomology X A B hA hB p q c
      ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementHomologyIso X A B hA hB (p + q)).hom
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B) (p + q) z)) = _
  rw [twoSupportRelativeCapHomology_comparison, twoSupportSmallCapHomology_left]

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCapHomology
