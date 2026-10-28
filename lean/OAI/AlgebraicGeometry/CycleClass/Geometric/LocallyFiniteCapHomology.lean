import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap
import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Locally Finite Cap Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology.Cycles

noncomputable section

/-!
# The cap product on actual locally finite homology

The proved Alexander–Whitney boundary formula makes the existing locally
finite cap operation descend through boundaries in both arguments. The
result uses the actual categorical singular cohomology and locally finite
singular homology groups, including degree zero.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicTopology.Products.CapBoundary

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] (X : TopCat.{0})

@[simp]
theorem locallyFiniteChainCast_symm_apply {m n : ℕ} (h : m = n)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m) :
    LocallyFiniteCap.Cycles.locallyFiniteChainCast X h.symm (LocallyFiniteCap.Cycles.locallyFiniteChainCast X h z) = z := by
  subst n
  rfl

/-- Degree transport commutes with the actual differential. -/
@[simp]
theorem differential_locallyFiniteChainCast {m n : ℕ} (h : m = n) (j : ℕ)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d n j (LocallyFiniteCap.Cycles.locallyFiniteChainCast X h z) =
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d m j z := by
  subst n
  rfl

/-- A cocycle caps a locally finite cycle to a locally finite cycle. -/
theorem locallyFiniteCap_mem_chainCycles (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)) :
    LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z.val ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q := by
  cases q with
  | zero => exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ q =>
    apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q _).mpr
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom
      (LocallyFiniteCap.Cycles.locallyFiniteCap X p (q + 1) c.val z.val) = 0
    rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
    change LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q (LocallyFiniteCap.Cycles.locallyFiniteCap X p (q + 1) c.val z.val) = 0
    rw [LocallyFiniteCap.Cycles.boundary_locallyFiniteCap X p q c.val z.val]
    have hz := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X)
      (p + q + 1) (p + q) z
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (p + q + 1) (p + q)).hom z.val = 0 at hz
    rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d] at hz
    change LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) z.val = 0 at hz
    have hc := AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X)
      p (p + 1) c
    simp only [hz, hc, map_zero, LinearMap.zero_apply, sub_self, smul_zero]

/-- The actual bilinear cap operation restricted to cocycles and locally finite cycles. -/
def locallyFiniteCapCycles (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) →ₗ[R]
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q where
  toFun c :=
    (((LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val).comp
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)).subtype).codRestrict
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q)
        (fun z => locallyFiniteCap_mem_chainCycles X p q c z))
  map_add' c d := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change LocallyFiniteCap.Cycles.locallyFiniteCap X p q (c.val + d.val) z.val =
      LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z.val + LocallyFiniteCap.Cycles.locallyFiniteCap X p q d.val z.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change LocallyFiniteCap.Cycles.locallyFiniteCap X p q (r • c.val) z.val = r • LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem locallyFiniteCapCycles_val (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)) :
    (locallyFiniteCapCycles X p q c z).val = LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val z.val := rfl

/-- A cocycle capped with a boundary has an explicit locally finite bounding chain. -/
theorem locallyFiniteCap_cocycle_boundary_exists (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (i : ℕ) (w : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).X i) :
    ∃ v : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).X (q + 1),
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q v =
        LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d i (p + q) w) := by
  by_cases hi : (ComplexShape.down ℕ).Rel i (p + q)
  · have hi' : p + q + 1 = i := hi
    subst i
    refine ⟨((-1 : ℤ) ^ p) • LocallyFiniteCap.Cycles.locallyFiniteCap X p (q + 1) c.val w, ?_⟩
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom
      (((-1 : ℤ) ^ p) • LocallyFiniteCap.Cycles.locallyFiniteCap X p (q + 1) c.val w) =
        LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val
          (((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (p + q + 1) (p + q)).hom w)
    rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d, LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
    change LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q
      (((-1 : ℤ) ^ p) • LocallyFiniteCap.Cycles.locallyFiniteCap X p (q + 1) c.val w) =
        LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) w)
    have h := LocallyFiniteCap.Cycles.locallyFiniteCap_boundary X p q c.val w
    have hc := AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X)
      p (p + 1) c
    simpa only [hc, map_zero, LinearMap.zero_apply, zero_add, map_zsmul] using h.symm
  · refine ⟨0, ?_⟩
    rw [(LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).shape i (p + q) hi]
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom 0 =
      LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val 0
    exact (map_zero ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom).trans
      (map_zero (LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val)).symm

/-- A coboundary capped with a locally finite cycle has an explicit
locally finite bounding chain; the off-shape case includes degree zero. -/
theorem locallyFiniteCap_coboundary_cycle_exists (i p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X i)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)) :
    ∃ v : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).X (q + 1),
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q v =
        LocallyFiniteCap.Cycles.locallyFiniteCap X p q ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d i p a) z.val := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · have hp : i + 1 = p := hip
    subst p
    have hdeg : (i + 1) + q = i + q + 1 := by omega
    let w := LocallyFiniteCap.Cycles.locallyFiniteChainCast X hdeg z.val
    have hw : LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (i + q) w = 0 := by
      rw [← LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
      change (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (i + q + 1) (i + q)
        (LocallyFiniteCap.Cycles.locallyFiniteChainCast X hdeg z.val) = 0
      rw [differential_locallyFiniteChainCast]
      exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X)
        ((i + 1) + q) (i + q) z
    have hb : LocallyFiniteCap.Cycles.locallyFiniteChainCast X (by omega : i + q + 1 = (i + 1) + q) w = z.val :=
      locallyFiniteChainCast_symm_apply X hdeg z.val
    have h := LocallyFiniteCap.Cycles.locallyFiniteCap_boundary X i q a w
    rw [hw, map_zero, hb] at h
    refine ⟨- (((-1 : ℤ) ^ i) • LocallyFiniteCap.Cycles.locallyFiniteCap X i (q + 1) a w), ?_⟩
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom
      (- (((-1 : ℤ) ^ i) • LocallyFiniteCap.Cycles.locallyFiniteCap X i (q + 1) a w)) =
        LocallyFiniteCap.Cycles.locallyFiniteCap X (i + 1) q
          ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d i (i + 1) a) z.val
    rw [LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d]
    change LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q
      (- (((-1 : ℤ) ^ i) • LocallyFiniteCap.Cycles.locallyFiniteCap X i (q + 1) a w)) =
        LocallyFiniteCap.Cycles.locallyFiniteCap X (i + 1) q
          ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d i (i + 1) a) z.val
    have heq : LocallyFiniteCap.Cycles.locallyFiniteCap X (i + 1) q
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d i (i + 1) a) z.val =
        - (((-1 : ℤ) ^ i) •
          LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q (LocallyFiniteCap.Cycles.locallyFiniteCap X i (q + 1) a w)) :=
      eq_neg_of_add_eq_zero_left h.symm
    simpa only [map_neg, map_zsmul] using heq.symm
  · refine ⟨0, ?_⟩
    rw [(AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).shape i p hip]
    change ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom 0 =
      LocallyFiniteCap.Cycles.locallyFiniteCap X p q 0 z.val
    calc
      _ = 0 := map_zero ((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q).hom
      _ = _ := by rw [map_zero]; rfl

/-- A fixed cocycle acts linearly on the actual locally finite homology group. -/
def locallyFiniteCapCocycleHomology (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p) :
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology (p + q) →ₗ[R]
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology q :=
  ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaries (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)).liftQ
    ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q).comp (locallyFiniteCapCycles X p q c))
    (by
      intro z hz
      rcases hz with ⟨w, rfl⟩
      change AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q
        (locallyFiniteCapCycles X p q c
          (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaryMap (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) w)) = 0
      apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q _).mpr
      change ∃ v : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).X (q + 1),
        (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q v =
          LocallyFiniteCap.Cycles.locallyFiniteCap X p q c.val (((LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).sc (p + q)).f w)
      exact locallyFiniteCap_cocycle_boundary_exists X p q c _ w)).comp
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.homologyQuotientIso (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)).toLinearEquiv.toLinearMap

@[simp]
theorem locallyFiniteCapCocycleHomology_chainClass (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)) :
    locallyFiniteCapCocycleHomology X p q c
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) z) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q (locallyFiniteCapCycles X p q c z) := by
  dsimp only [locallyFiniteCapCocycleHomology, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- The induced action is also linear in the ordinary cocycle. -/
def locallyFiniteCocycleCapHomology (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p →ₗ[R]
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology (p + q) →ₗ[R]
        (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology q where
  toFun := locallyFiniteCapCocycleHomology X p q
  map_add' c d := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) h
    simp only [locallyFiniteCapCocycleHomology_chainClass, LinearMap.add_apply, map_add]
  map_smul' r c := by
    apply LinearMap.ext
    intro h
    obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) h
    simp only [locallyFiniteCapCocycleHomology_chainClass, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- A coboundary acts trivially on genuine locally finite homology. -/
@[simp]
theorem locallyFiniteCocycleCapHomology_boundary (p q : ℕ)
    (a : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).sc p).X₁) :
    locallyFiniteCocycleCapHomology X p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p a) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) h
  change locallyFiniteCapCocycleHomology X p q
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p a)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) z) = 0
  rw [locallyFiniteCapCocycleHomology_chainClass]
  apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q _).mpr
  change ∃ v : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).X (q + 1),
    (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).d (q + 1) q v =
      LocallyFiniteCap.Cycles.locallyFiniteCap X p q (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).sc p).f a) z.val
  exact locallyFiniteCap_coboundary_cycle_exists X _ p q a z

/-- The actual bilinear cap product of ordinary cohomology and locally
finite homology. No duality or orientation theorem is assumed. -/
def locallyFiniteCapHomology (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p →ₗ[R]
      (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology (p + q) →ₗ[R]
        (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X).homology q :=
  ((AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p).liftQ
    (locallyFiniteCocycleCapHomology X p q)
    (by
      intro c hc
      rcases hc with ⟨a, rfl⟩
      exact locallyFiniteCocycleCapHomology_boundary X p q a)).comp
    (AlgebraicTopology.Cohomology.Singular.Representatives.cohomologyQuotientIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p).toLinearEquiv.toLinearMap

/-- On represented classes, the descended product is the class of the
previously constructed locally finite Alexander–Whitney cap chain. -/
@[simp]
theorem locallyFiniteCapHomology_class_class (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q)) :
    locallyFiniteCapHomology X p q (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) z) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q (locallyFiniteCapCycles X p q c z) := by
  dsimp only [locallyFiniteCapHomology, AlgebraicTopology.Cohomology.Singular.Representatives.singularClass, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact locallyFiniteCapCocycleHomology_chainClass X p q c z

/-- Replacing either representative without changing its actual class
does not alter the output homology class. -/
theorem locallyFiniteCapHomology_independent (p q : ℕ)
    (c c' : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z z' : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q))
    (hc : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c')
    (hz : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) z =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) (p + q) z') :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q (locallyFiniteCapCycles X p q c z) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q (locallyFiniteCapCycles X p q c' z') := by
  rw [← locallyFiniteCapHomology_class_class, ← locallyFiniteCapHomology_class_class, hc, hz]

/-- On ordinary cycle representatives, locally finite cap agrees with the
ordinary cap followed by the canonical finite-chain inclusion. -/
theorem locallyFiniteCapCycles_ordinary (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) (p + q)) :
    locallyFiniteCapCycles X p q c (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) (p + q) z) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) q
        (AlgebraicTopology.Products.CapBoundary.capCycles (TopCat.toSSet.obj X) p q c z) := by
  apply Subtype.ext
  exact LocallyFiniteCap.Cycles.locallyFiniteCap_ordinary X p q c.val z.val

/-- The descended product extends the existing ordinary cap product on
actual homology through the canonical ordinary-to-locally-finite map. -/
theorem locallyFiniteCapHomology_ordinary (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology (p + q)) :
    locallyFiniteCapHomology X p q c
        (HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) (p + q) z) =
      HomologicalComplex.homologyMap (LocallyFiniteComparison.Cycles.ordinaryToLocallyFiniteChainMap R X) q
        (AlgebraicTopology.Products.CapBoundary.singularCapHomology X p q c z) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p c
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) (p + q) z
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, locallyFiniteCapHomology_class_class,
    AlgebraicTopology.Products.CapBoundary.singularCapHomology_class_class, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  exact congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex R X) q)
    (locallyFiniteCapCycles_ordinary X p q c z)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCapHomology.Cycles
