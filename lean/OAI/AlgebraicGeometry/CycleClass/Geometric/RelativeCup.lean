import OAI.AlgebraicTopology.Products.CupBoundaries
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy

/-! # Relative Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup

noncomputable section

/-!
# Cup products on actual relative singular cochains

The ordinary front/back cup pairing preserves the kernel of restriction when
either factor is relative. We lift it through the proved injective relative
cochain inclusion. All products therefore live in the existing categorical
relative singular cochain complex and recover the ordinary cup after inclusion.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology OAI.AlgebraicTopology.Products.CupBoundaries

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {R : Type} [CommRing R]

/-- Equality of degrees transports elements of the actual relative complex. -/
def relativeCochainCast (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {m n : ℕ} (h : m = n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X m →ₗ[R]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n := by
  subst n
  exact LinearMap.id

@[simp]
theorem relativeCochainCast_rfl (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    {n : ℕ} (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    relativeCochainCast M X A rfl c = c := rfl

@[simp]
theorem relativeCochainCast_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) {m n : ℕ} (h : m = n)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X m) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n (relativeCochainCast M X A h c) =
      AlgebraicTopology.Products.Cup.cochainCast (TopCat.toSSet.obj X) M h ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f m c) := by
  subst n
  rfl

private def relativeCupLift (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n c = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n :=
  (LinearEquiv.ofInjective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n).hom
    (RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective M X A n)).symm
      ⟨c, by rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]; exact hc⟩

@[simp]
private theorem relativeCupLift_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n c = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n (relativeCupLift M X A n c hc) = c := by
  simp [relativeCupLift]

private theorem relativeCup_restriction_zero (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) = 0 :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M X A) n) c

private theorem relativeCup_inclusion_d (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (m n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X m) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d m n c) =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d m n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f m c) :=
  (ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).comm m n) c).symm

private theorem relativeCup_inclusion_pullback (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {D : Set Y}
    (hf : Set.MapsTo f A D) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y D).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf).f n c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y D).f n c) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f hf) n) c

/-- The ordinary front/back pairing is natural for genuine continuous maps. -/
theorem cupWith_singularPullback {X Y : TopCat.{0}} (f : X ⟶ Y)
    {M N L : ModuleCat.{0} R} (B : M →ₗ[R] N →ₗ[R] L) {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y).X p) (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N Y).X q) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback L f).f (p + q) (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj Y) B c d) =
      AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f p c) ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback N f).f q d) :=
  AlgebraicTopology.Products.Cup.cupWith_pullback (TopCat.toSSet.map f) B c d

variable (X : TopCat.{0}) (A : Set X)
  {M N L : ModuleCat.{0} R} (B : M →ₗ[R] N →ₗ[R] L)

/-- Restriction annihilates an ordinary cup whose right factor is relative. -/
theorem absoluteRelativeCupWith_restriction_zero {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction L X A).f (p + q)
      (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B c ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion N X A).f q d)) = 0 := by
  rw [cupWith_singularPullback, relativeCup_restriction_zero, AlgebraicTopology.Products.Cup.cupWith_zero_right]

/-- Restriction annihilates an ordinary cup whose left factor is relative. -/
theorem relativeAbsoluteCupWith_restriction_zero {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction L X A).f (p + q)
      (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f p c) d) = 0 := by
  rw [cupWith_singularPullback, relativeCup_restriction_zero, AlgebraicTopology.Products.Cup.cupWith_zero_left]

/-- Absolute cochains cup relative cochains inside the actual relative kernel. -/
def absoluteRelativeCupWith (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p →ₗ[R]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q →ₗ[R]
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).X (p + q) where
  toFun c :=
    { toFun d := relativeCupLift L X A (p + q)
        (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B c ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion N X A).f q d))
        (absoluteRelativeCupWith_restriction_zero X A B c d)
      map_add' d e := by
        apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
        simp only [relativeCupLift_inclusion, map_add, AlgebraicTopology.Products.Cup.cupWith_add_right]
      map_smul' r d := by
        apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
        simp only [relativeCupLift_inclusion, map_smul, AlgebraicTopology.Products.Cup.cupWith_smul_right, RingHom.id_apply] }
  map_add' c e := by
    apply LinearMap.ext
    intro d
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
    simp only [relativeCupLift_inclusion, map_add, AlgebraicTopology.Products.Cup.cupWith_add_left]
  map_smul' r c := by
    apply LinearMap.ext
    intro d
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
    simp only [relativeCupLift_inclusion, map_smul, AlgebraicTopology.Products.Cup.cupWith_smul_left]

/-- Relative cochains cup absolute cochains inside the same actual kernel. -/
def relativeAbsoluteCupWith (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p →ₗ[R]
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q →ₗ[R]
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).X (p + q) where
  toFun c :=
    { toFun d := relativeCupLift L X A (p + q)
        (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f p c) d)
        (relativeAbsoluteCupWith_restriction_zero X A B c d)
      map_add' d e := by
        apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
        simp only [relativeCupLift_inclusion, map_add, AlgebraicTopology.Products.Cup.cupWith_add_right]
      map_smul' r d := by
        apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
        simp only [relativeCupLift_inclusion, map_smul, AlgebraicTopology.Products.Cup.cupWith_smul_right, RingHom.id_apply] }
  map_add' c e := by
    apply LinearMap.ext
    intro d
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
    simp only [relativeCupLift_inclusion, map_add, AlgebraicTopology.Products.Cup.cupWith_add_left]
  map_smul' r c := by
    apply LinearMap.ext
    intro d
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
    simp only [relativeCupLift_inclusion, map_smul, AlgebraicTopology.Products.Cup.cupWith_smul_left]

/-- Inclusion recovers the original front/back pairing, with the right
relative factor included into the absolute complex. -/
@[simp]
theorem absoluteRelativeCupWith_inclusion {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion L X A).f (p + q) (absoluteRelativeCupWith X A B p q c d) =
      AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B c ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion N X A).f q d) := by
  exact relativeCupLift_inclusion L X A (p + q) _
    (absoluteRelativeCupWith_restriction_zero X A B c d)

/-- Inclusion recovers the original front/back pairing in the opposite
absolute/relative order as well. -/
@[simp]
theorem relativeAbsoluteCupWith_inclusion {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion L X A).f (p + q) (relativeAbsoluteCupWith X A B p q c d) =
      AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f p c) d := by
  exact relativeCupLift_inclusion L X A (p + q) _
    (relativeAbsoluteCupWith_restriction_zero X A B c d)

/-- The actual relative differential obeys the front/back Leibniz formula,
with the first degree identification explicit and the usual sign. -/
theorem absoluteRelativeCupWith_coboundary {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).d (p + q) (p + q + 1)
        (absoluteRelativeCupWith X A B p q c d) =
      relativeCochainCast L X A (by omega : (p + 1) + q = p + q + 1)
        (absoluteRelativeCupWith X A B (p + 1) q
          ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d p (p + 1) c) d) +
      (-1 : ℤ) ^ p • absoluteRelativeCupWith X A B p (q + 1) c
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).d q (q + 1) d) := by
  apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q + 1)
  simp only [relativeCup_inclusion_d, absoluteRelativeCupWith_inclusion,
    map_add, map_zsmul, relativeCochainCast_inclusion]
  have hright : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion L X A).f (p + q + 1)
      (absoluteRelativeCupWith X A B p (q + 1) c
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).d q (q + 1) d)) =
      AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B c ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion N X A).f (q + 1)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).d q (q + 1) d)) :=
    absoluteRelativeCupWith_inclusion X A B c
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).d q (q + 1) d)
  rw [hright, relativeCup_inclusion_d]
  exact AlgebraicTopology.Products.Cup.cupWith_coboundary (TopCat.toSSet.obj X) B c
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion N X A).f q d)

/-- The same Leibniz formula holds with the relative factor on the left;
the sign still depends on its actual first degree. -/
theorem relativeAbsoluteCupWith_coboundary {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).d (p + q) (p + q + 1)
        (relativeAbsoluteCupWith X A B p q c d) =
      relativeCochainCast L X A (by omega : (p + 1) + q = p + q + 1)
        (relativeAbsoluteCupWith X A B (p + 1) q
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d p (p + 1) c) d) +
      (-1 : ℤ) ^ p • relativeAbsoluteCupWith X A B p (q + 1) c
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d q (q + 1) d) := by
  apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q + 1)
  simp only [relativeCup_inclusion_d, relativeAbsoluteCupWith_inclusion,
    map_add, map_zsmul, relativeCochainCast_inclusion]
  have hright : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion L X A).f (p + q + 1)
      (relativeAbsoluteCupWith X A B p (q + 1) c
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d q (q + 1) d)) =
      AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) B ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f p c)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d q (q + 1) d) :=
    relativeAbsoluteCupWith_inclusion X A B c ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d q (q + 1) d)
  rw [hright]
  exact AlgebraicTopology.Products.Cup.cupWith_coboundary (TopCat.toSSet.obj X) B
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f p c) d

/-- Closed absolute and relative factors give a closed actual relative cochain. -/
theorem absoluteRelativeCupWith_cocycles {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q)
    (hc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d p (p + 1) c = 0)
    (hd : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).d q (q + 1) d = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).d (p + q) (p + q + 1)
      (absoluteRelativeCupWith X A B p q c d) = 0 := by
  rw [absoluteRelativeCupWith_coboundary, hc, hd]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- The analogous actual relative cocycle statement in the opposite order. -/
theorem relativeAbsoluteCupWith_cocycles {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q)
    (hc : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).d p (p + 1) c = 0)
    (hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d q (q + 1) d = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains L X A).d (p + q) (p + q + 1)
      (relativeAbsoluteCupWith X A B p q c d) = 0 := by
  rw [relativeAbsoluteCupWith_coboundary, hc, hd]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-- Pullback by a genuine continuous map of pairs preserves the
absolute-relative cup already at the cochain level. -/
theorem absoluteRelativeCupWith_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M Y).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N Y D).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap L f hf).f (p + q)
        (absoluteRelativeCupWith Y D B p q c d) =
      absoluteRelativeCupWith X A B p q ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f p c)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap N f hf).f q d) := by
  apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
  simp only [relativeCup_inclusion_pullback, absoluteRelativeCupWith_inclusion,
    cupWith_singularPullback]

/-- Pullback by the same actual pair map preserves relative-absolute cup. -/
theorem relativeAbsoluteCupWith_pullback {Y : TopCat.{0}}
    (f : X ⟶ Y) {D : Set Y} (hf : Set.MapsTo f A D) {p q : ℕ}
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y D).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N Y).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap L f hf).f (p + q)
        (relativeAbsoluteCupWith Y D B p q c d) =
      relativeAbsoluteCupWith X A B p q ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf).f p c)
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback N f).f q d) := by
  apply RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective L X A (p + q)
  simp only [relativeCup_inclusion_pullback, relativeAbsoluteCupWith_inclusion,
    cupWith_singularPullback]

/-- Shrinking the removed subset, equivalently enlarging the allowed support,
commutes with absolute-relative cup through the genuine identity pair map. -/
theorem absoluteRelativeCupWith_supportEnlargement {D : Set X} (hDA : D ⊆ A)
    {p q : ℕ} (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains N X A).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap L (𝟙 X) hDA).f (p + q)
        (absoluteRelativeCupWith X A B p q c d) =
      absoluteRelativeCupWith X D B p q c
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap N (𝟙 X) hDA).f q d) := by
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, HomologicalComplex.id_f, ConcreteCategory.id_apply] using
    absoluteRelativeCupWith_pullback X D B (𝟙 X) hDA c d

/-- The same support enlargement commutes with relative-absolute cup. -/
theorem relativeAbsoluteCupWith_supportEnlargement {D : Set X} (hDA : D ⊆ A)
    {p q : ℕ} (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X p)
    (d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X q) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap L (𝟙 X) hDA).f (p + q)
        (relativeAbsoluteCupWith X A B p q c d) =
      relativeAbsoluteCupWith X D B p q
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 X) hDA).f p c) d := by
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, HomologicalComplex.id_f, ConcreteCategory.id_apply] using
    relativeAbsoluteCupWith_pullback X D B (𝟙 X) hDA c d

/-- The scalar front/back cup with an absolute first and relative second factor. -/
abbrev absoluteRelativeCup (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p →ₗ[R]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).X q →ₗ[R]
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).X (p + q) :=
  absoluteRelativeCupWith X A (LinearMap.mul R R) p q

/-- The scalar front/back cup with a relative first and absolute second factor. -/
abbrev relativeAbsoluteCup (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).X p →ₗ[R]
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X q →ₗ[R]
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).X (p + q) :=
  relativeAbsoluteCupWith X A (LinearMap.mul R R) p q

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup
