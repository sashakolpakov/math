import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.CocycleBilinearDescent
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Relative Cup Cohomology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology

noncomputable section

/-!
# The cup product on actual relative singular cohomology

The genuine front/back pairing on relative cochains descends through the
actual cocycle and coboundary quotients. The boundary proofs exhibit cup
primitives, with the sign in the second slot and the zero-degree case treated
explicitly. Naturality and forgetting support follow on representatives.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CupCohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {R : Type} [CommRing R]

/-- Transport an actual relative cocycle along an equality of degrees. -/
def relativeCocycleCast (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) m →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n := by
  subst n
  exact LinearMap.id

/-- Transport actual relative cohomology along an equality of degrees. -/
def relativeCohomologyCast (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A m →ₗ[R] AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n := by
  subst n
  exact LinearMap.id

@[simp]
theorem relativeCocycleCast_val (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) m) :
    (relativeCocycleCast M X A h c).val = RelativeCup.Cycles.relativeCochainCast M X A h c.val := by
  subst n
  rfl

@[simp]
theorem relativeCohomologyCast_class (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) m) :
    relativeCohomologyCast M X A h (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) m c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n (relativeCocycleCast M X A h c) := by
  subst n
  rfl

private theorem relativeCup_incoming_zero (C : CochainComplex (ModuleCat.{0} R) ℕ) :
    (C.sc 0).f = 0 := by
  change C.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  apply C.shape
  change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
  omega

private theorem relativeCup_boundary_succ_iff
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (x : C.X (n + 1)) :
    (∃ z : (C.sc (n + 1)).X₁, (C.sc (n + 1)).f z = x) ↔
      ∃ z : C.X n, C.d n (n + 1) z = x := by
  change (∃ z : C.X ((ComplexShape.up ℕ).prev (n + 1)),
    C.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) z = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

private theorem relativeCup_boundary_cast_iff (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) {m n : ℕ} (h : m = n)
    (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X m) :
    (∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc m).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc m).f z = x) ↔
    ∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc n).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc n).f z = RelativeCup.Cycles.relativeCochainCast M X A h x := by
  subst n
  rfl

variable (X : TopCat.{0}) (A : Set X)
  {M N L : ModuleCat.{0} R} (B : M →ₗ[R] N →ₗ[R] L)

/-- Cup of an actual left coboundary with a cocycle has the cup of its
primitive as a relative primitive; incoming degree zero is handled by zero. -/
theorem absoluteRelativeCupWith_boundary_left (p q : ℕ)
    (b : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q) :
    ∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).f z =
        RelativeCup.Cycles.absoluteRelativeCupWith X A B p q (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc p).f b) d.val := by
  cases p with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, relativeCup_incoming_zero (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X)]
      change 0 = RelativeCup.Cycles.absoluteRelativeCupWith X A B 0 q 0 d.val
      simp only [map_zero, LinearMap.zero_apply]
  | succ p =>
      obtain ⟨a, ha⟩ := (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc (p + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (relativeCup_boundary_cast_iff L X A
        (by omega : (p + 1) + q = p + q + 1)
        (RelativeCup.Cycles.absoluteRelativeCupWith X A B (p + 1) q ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d p (p + 1) a) d.val)).mpr
      apply (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) _).mpr
      refine ⟨RelativeCup.Cycles.absoluteRelativeCupWith X A B p q a d.val, ?_⟩
      have hd := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q d.val).mp d.property
      rw [RelativeCup.Cycles.absoluteRelativeCupWith_coboundary, hd]
      simp only [map_zero, smul_zero, add_zero]

/-- In positive right degree the actual primitive is
`(-1: ℤ)^p • cup(c, primitive)`; degree zero uses the zero cochain. -/
theorem absoluteRelativeCupWith_boundary_right (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p) (b : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).sc q).X₁) :
    ∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).f z =
        RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val (((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).sc q).f b) := by
  cases q with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, relativeCup_incoming_zero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A)]
      change 0 = RelativeCup.Cycles.absoluteRelativeCupWith X A B p 0 c.val 0
      simp only [map_zero]
  | succ q =>
      obtain ⟨a, ha⟩ := (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q
        (((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).sc (q + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) _).mpr
      refine ⟨(-1 : ℤ) ^ p • RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val a, ?_⟩
      have hc := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p c.val).mp c.property
      rw [map_zsmul, RelativeCup.Cycles.absoluteRelativeCupWith_coboundary, hc]
      simp only [map_zero, LinearMap.zero_apply, zero_add]
      rw [smul_smul, ← mul_pow]
      simp

/-- Restrict the genuine relative cup pairing to its actual cocycle kernels. -/
def absoluteRelativeCocycleCupWith (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) where
  toFun c :=
    { toFun d := ⟨RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val d.val, by
        rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
        exact RelativeCup.Cycles.absoluteRelativeCupWith_cocycles X A B c.val d.val
          ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p c.val).mp c.property)
          ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q d.val).mp d.property)⟩
      map_add' d e := Subtype.ext ((RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val).map_add d.val e.val)
      map_smul' r d := Subtype.ext ((RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val).map_smul r d.val) }
  map_add' c e := by
    apply LinearMap.ext
    intro d
    apply Subtype.ext
    change RelativeCup.Cycles.absoluteRelativeCupWith X A B p q (c.val + e.val) d.val =
      RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val d.val + RelativeCup.Cycles.absoluteRelativeCupWith X A B p q e.val d.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro d
    apply Subtype.ext
    change RelativeCup.Cycles.absoluteRelativeCupWith X A B p q (r • c.val) d.val =
      r • RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val d.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem absoluteRelativeCocycleCupWith_val {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q) :
    (absoluteRelativeCocycleCupWith X A B p q c d).val =
      RelativeCup.Cycles.absoluteRelativeCupWith X A B p q c.val d.val := rfl

/-- The actual boundary submodule in the first slot maps into boundaries. -/
theorem absoluteRelativeCocycleCupWith_boundary_left (p q : ℕ)
    (b : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q) :
    absoluteRelativeCocycleCupWith X A B p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p b) d ∈
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) := by
  obtain ⟨z, hz⟩ := absoluteRelativeCupWith_boundary_left X A B p q b d
  exact ⟨z, Subtype.ext hz⟩

/-- The actual boundary submodule in the second slot maps into boundaries. -/
theorem absoluteRelativeCocycleCupWith_boundary_right (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p) (b : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).sc q).X₁) :
    absoluteRelativeCocycleCupWith X A B p q c (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q b) ∈
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) := by
  obtain ⟨z, hz⟩ := absoluteRelativeCupWith_boundary_right X A B p q c b
  exact ⟨z, Subtype.ext hz⟩

/-- The genuine relative cup pairing on categorical cohomology, obtained
by descending the proved cochain operation through both actual quotients. -/
def absoluteRelativeCohomologyCupWith (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).homology p →ₗ[R] (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).homology q →ₗ[R] (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).homology (p + q) :=
  CocycleBilinearDescent.Cycles.cohomologyBilinearOfCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) p q (p + q)
    (absoluteRelativeCocycleCupWith X A B p q)
    (absoluteRelativeCocycleCupWith_boundary_left X A B p q)
    (absoluteRelativeCocycleCupWith_boundary_right X A B p q)

/-- Any actual cocycle representatives compute the descended product. -/
@[simp]
theorem absoluteRelativeCohomologyCupWith_class_class {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q) :
    absoluteRelativeCohomologyCupWith X A B p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q d) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) (absoluteRelativeCocycleCupWith X A B p q c d) :=
  CocycleBilinearDescent.Cycles.cohomologyBilinearOfCocycles_class_class (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) p q (p + q)
    (absoluteRelativeCocycleCupWith X A B p q)
    (absoluteRelativeCocycleCupWith_boundary_left X A B p q)
    (absoluteRelativeCocycleCupWith_boundary_right X A B p q) c d

/-- Cup of an actual left coboundary with a cocycle has the cup of its
primitive as a relative primitive; incoming degree zero is handled by zero. -/
theorem relativeAbsoluteCupWith_boundary_left (p q : ℕ)
    (b : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q) :
    ∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).f z =
        RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q (((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc p).f b) d.val := by
  cases p with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, relativeCup_incoming_zero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A)]
      change 0 = RelativeCup.Cycles.relativeAbsoluteCupWith X A B 0 q 0 d.val
      simp only [map_zero, LinearMap.zero_apply]
  | succ p =>
      obtain ⟨a, ha⟩ := (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p
        (((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc (p + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (relativeCup_boundary_cast_iff L X A
        (by omega : (p + 1) + q = p + q + 1)
        (RelativeCup.Cycles.relativeAbsoluteCupWith X A B (p + 1) q ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d p (p + 1) a) d.val)).mpr
      apply (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) _).mpr
      refine ⟨RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q a d.val, ?_⟩
      have hd := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q d.val).mp d.property
      rw [RelativeCup.Cycles.relativeAbsoluteCupWith_coboundary, hd]
      simp only [map_zero, smul_zero, add_zero]

/-- In positive right degree the actual primitive is
`(-1: ℤ)^p • cup(c, primitive)`; degree zero uses the zero cochain. -/
theorem relativeAbsoluteCupWith_boundary_right (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p) (b : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc q).X₁) :
    ∃ z : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).X₁,
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).sc (p + q)).f z =
        RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc q).f b) := by
  cases q with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, relativeCup_incoming_zero (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X)]
      change 0 = RelativeCup.Cycles.relativeAbsoluteCupWith X A B p 0 c.val 0
      simp only [map_zero]
  | succ q =>
      obtain ⟨a, ha⟩ := (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc (q + 1)).f b)).mp ⟨b, rfl⟩
      rw [← ha]
      apply (relativeCup_boundary_succ_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) _).mpr
      refine ⟨(-1 : ℤ) ^ p • RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val a, ?_⟩
      have hc := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p c.val).mp c.property
      rw [map_zsmul, RelativeCup.Cycles.relativeAbsoluteCupWith_coboundary, hc]
      simp only [map_zero, LinearMap.zero_apply, zero_add]
      rw [smul_smul, ← mul_pow]
      simp

/-- Restrict the genuine relative cup pairing to its actual cocycle kernels. -/
def relativeAbsoluteCocycleCupWith (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p →ₗ[R] AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) where
  toFun c :=
    { toFun d := ⟨RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val d.val, by
        rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
        exact RelativeCup.Cycles.relativeAbsoluteCupWith_cocycles X A B c.val d.val
          ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p c.val).mp c.property)
          ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q d.val).mp d.property)⟩
      map_add' d e := Subtype.ext ((RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val).map_add d.val e.val)
      map_smul' r d := Subtype.ext ((RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val).map_smul r d.val) }
  map_add' c e := by
    apply LinearMap.ext
    intro d
    apply Subtype.ext
    change RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q (c.val + e.val) d.val =
      RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val d.val + RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q e.val d.val
    simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro d
    apply Subtype.ext
    change RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q (r • c.val) d.val =
      r • RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val d.val
    simp only [map_smul, LinearMap.smul_apply]

@[simp]
theorem relativeAbsoluteCocycleCupWith_val {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q) :
    (relativeAbsoluteCocycleCupWith X A B p q c d).val =
      RelativeCup.Cycles.relativeAbsoluteCupWith X A B p q c.val d.val := rfl

/-- The actual boundary submodule in the first slot maps into boundaries. -/
theorem relativeAbsoluteCocycleCupWith_boundary_left (p q : ℕ)
    (b : ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).sc p).X₁) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q) :
    relativeAbsoluteCocycleCupWith X A B p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p b) d ∈
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) := by
  obtain ⟨z, hz⟩ := relativeAbsoluteCupWith_boundary_left X A B p q b d
  exact ⟨z, Subtype.ext hz⟩

/-- The actual boundary submodule in the second slot maps into boundaries. -/
theorem relativeAbsoluteCocycleCupWith_boundary_right (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p) (b : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc q).X₁) :
    relativeAbsoluteCocycleCupWith X A B p q c (AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaryMap (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q b) ∈
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainBoundaries (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) := by
  obtain ⟨z, hz⟩ := relativeAbsoluteCupWith_boundary_right X A B p q c b
  exact ⟨z, Subtype.ext hz⟩

/-- The genuine relative cup pairing on categorical cohomology, obtained
by descending the proved cochain operation through both actual quotients. -/
def relativeAbsoluteCohomologyCupWith (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).homology p →ₗ[R] (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).homology q →ₗ[R] (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).homology (p + q) :=
  CocycleBilinearDescent.Cycles.cohomologyBilinearOfCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) p q (p + q)
    (relativeAbsoluteCocycleCupWith X A B p q)
    (relativeAbsoluteCocycleCupWith_boundary_left X A B p q)
    (relativeAbsoluteCocycleCupWith_boundary_right X A B p q)

/-- Any actual cocycle representatives compute the descended product. -/
@[simp]
theorem relativeAbsoluteCohomologyCupWith_class_class {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q) :
    relativeAbsoluteCohomologyCupWith X A B p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q d) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) (p + q) (relativeAbsoluteCocycleCupWith X A B p q c d) :=
  CocycleBilinearDescent.Cycles.cohomologyBilinearOfCocycles_class_class (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A) p q (p + q)
    (relativeAbsoluteCocycleCupWith X A B p q)
    (relativeAbsoluteCocycleCupWith_boundary_left X A B p q)
    (relativeAbsoluteCocycleCupWith_boundary_right X A B p q) c d

/-- Forgetting relative support recovers the actual ordinary cup pairing. -/
theorem absoluteRelativeCohomologyCupWith_inclusion (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion L X A (p + q)
        (absoluteRelativeCohomologyCupWith X A B p q x y) =
      AlgebraicTopology.Products.CupCohomology.cohomologyCupWith (TopCat.toSSet.obj X) B p q (x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion N X A q y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q y
  simp only [absoluteRelativeCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.absoluteRelativeCupWith_inclusion X A B c.val d.val

/-- The actual pair pullback preserves the relative cohomology cup product. -/
theorem absoluteRelativeCohomologyCupWith_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N Y D).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap L f hf (p + q)
        (absoluteRelativeCohomologyCupWith Y D B p q x y) =
      absoluteRelativeCohomologyCupWith X A B p q (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M f p x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap N f hf q y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N Y D) q y
  simp only [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback, absoluteRelativeCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.absoluteRelativeCupWith_pullback X A B f hf c.val d.val

/-- Enlarging the allowed support commutes with the actual relative cup. -/
theorem absoluteRelativeCohomologyCupWith_supportEnlargement {D : Set X}
    (hDA : D ⊆ A) (p q : ℕ) (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap L (𝟙 X) hDA (p + q)
        (absoluteRelativeCohomologyCupWith X A B p q x y) =
      absoluteRelativeCohomologyCupWith X D B p q (x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap N (𝟙 X) hDA q y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A) q y
  simp only [absoluteRelativeCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.absoluteRelativeCupWith_supportEnlargement X A B hDA c.val d.val

/-- The scalar relative cup product on actual singular cohomology. -/
abbrev absoluteRelativeCohomologyCup (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology p →ₗ[R] (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology q →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A (p + q) :=
  absoluteRelativeCohomologyCupWith X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q

@[simp]
theorem absoluteRelativeCohomologyCup_class_class {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) q) :
    absoluteRelativeCohomologyCup (R := R) X A p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) q d) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) (p + q)
          (absoluteRelativeCocycleCupWith X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q c d) :=
  absoluteRelativeCohomologyCupWith_class_class X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) c d

theorem absoluteRelativeCohomologyCup_inclusion (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of R R) X A (p + q)
        (absoluteRelativeCohomologyCup (R := R) X A p q x y) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p q (x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of R R) X A q y) :=
  absoluteRelativeCohomologyCupWith_inclusion X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q x y

theorem absoluteRelativeCohomologyCup_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) Y D).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) f hf (p + q)
        (absoluteRelativeCohomologyCup (R := R) Y D p q x y) =
      absoluteRelativeCohomologyCup (R := R) X A p q (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f p x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) f hf q y) :=
  absoluteRelativeCohomologyCupWith_pullback X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) f hf p q x y

theorem absoluteRelativeCohomologyCup_supportEnlargement {D : Set X}
    (hDA : D ⊆ A) (p q : ℕ) (x : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology p) (y : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) (𝟙 X) hDA (p + q)
        (absoluteRelativeCohomologyCup (R := R) X A p q x y) =
      absoluteRelativeCohomologyCup (R := R) X D p q (x) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) (𝟙 X) hDA q y) :=
  absoluteRelativeCohomologyCupWith_supportEnlargement X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) hDA p q x y

/-- Forgetting relative support recovers the actual ordinary cup pairing. -/
theorem relativeAbsoluteCohomologyCupWith_inclusion (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion L X A (p + q)
        (relativeAbsoluteCohomologyCupWith X A B p q x y) =
      AlgebraicTopology.Products.CupCohomology.cohomologyCupWith (TopCat.toSSet.obj X) B p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X A p x) (y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q y
  simp only [relativeAbsoluteCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion X A B c.val d.val

/-- The actual pair pullback preserves the relative cohomology cup product. -/
theorem relativeAbsoluteCohomologyCupWith_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y D).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N Y).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap L f hf (p + q)
        (relativeAbsoluteCohomologyCupWith Y D B p q x y) =
      relativeAbsoluteCohomologyCupWith X A B p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hf p x) (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback N f q y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y D) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N Y) q y
  simp only [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback, relativeAbsoluteCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.relativeAbsoluteCupWith_pullback X A B f hf c.val d.val

/-- Enlarging the allowed support commutes with the actual relative cup. -/
theorem relativeAbsoluteCohomologyCupWith_supportEnlargement {D : Set X}
    (hDA : D ⊆ A) (p q : ℕ) (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap L (𝟙 X) hDA (p + q)
        (relativeAbsoluteCohomologyCupWith X A B p q x y) =
      relativeAbsoluteCohomologyCupWith X D B p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (𝟙 X) hDA p x) (y) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) p x
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X) q y
  simp only [relativeAbsoluteCohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  congr 1
  apply Subtype.ext
  exact RelativeCup.Cycles.relativeAbsoluteCupWith_supportEnlargement X A B hDA c.val d.val

/-- The scalar relative cup product on actual singular cohomology. -/
abbrev relativeAbsoluteCohomologyCup (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology p →ₗ[R] (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology q →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A (p + q) :=
  relativeAbsoluteCohomologyCupWith X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q

@[simp]
theorem relativeAbsoluteCohomologyCup_class_class {p q : ℕ}
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) p) (d : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) q) :
    relativeAbsoluteCohomologyCup (R := R) X A p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) p c) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) q d) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) (p + q)
          (relativeAbsoluteCocycleCupWith X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q c d) :=
  relativeAbsoluteCohomologyCupWith_class_class X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) c d

theorem relativeAbsoluteCohomologyCup_inclusion (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of R R) X A (p + q)
        (relativeAbsoluteCohomologyCup (R := R) X A p q x y) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := R) X p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of R R) X A p x) (y) :=
  relativeAbsoluteCohomologyCupWith_inclusion X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) p q x y

theorem relativeAbsoluteCohomologyCup_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) (p q : ℕ)
    (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) Y D).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) f hf (p + q)
        (relativeAbsoluteCohomologyCup (R := R) Y D p q x y) =
      relativeAbsoluteCohomologyCup (R := R) X A p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) f hf p x) (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f q y) :=
  relativeAbsoluteCohomologyCupWith_pullback X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) f hf p q x y

theorem relativeAbsoluteCohomologyCup_supportEnlargement {D : Set X}
    (hDA : D ⊆ A) (p q : ℕ) (x : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).homology p) (y : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).homology q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) (𝟙 X) hDA (p + q)
        (relativeAbsoluteCohomologyCup (R := R) X A p q x y) =
      relativeAbsoluteCohomologyCup (R := R) X D p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of R R) (𝟙 X) hDA p x) (y) :=
  relativeAbsoluteCohomologyCupWith_supportEnlargement X A (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R) (LinearMap.mul R R) hDA p q x y

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology
