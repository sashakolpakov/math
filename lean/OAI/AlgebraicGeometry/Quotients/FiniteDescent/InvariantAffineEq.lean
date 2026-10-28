import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Invariant
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeNorm
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodOpen

/-! # Invariant Affine Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq.Construction.InvariantAffine

/-!
# Affineness of invariant cores

A principal open in an affine neighborhood can be made invariant using a
finite-free norm. The norm is taken only on the affine restriction of the
relation source; no global section on a nonaffine open is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {R X Y : Scheme.{u}} {s t : R ⟶ X} [IsFinite s]

/-- A norm on the restricted source describes the invariant core, provided
its nonvanishing records whether the relation target stays in the open. -/
theorem preimage_core_eq_norm (D : X.Opens) [IsAffine D] [IsAffine Y]
    (j : Y ⟶ R) (s' : Y ⟶ D.toScheme) (hs : IsPullback s' j D.ι s)
    {ι : Type v} [Fintype ι]
    (b : letI := s'.appTop.hom.toAlgebra; Module.Basis ι Γ(D, ⊤) Γ(Y, ⊤))
    (a : Γ(Y, ⊤)) (ha : (j ≫ t) ⁻¹ᵁ D = Y.basicOpen a) :
    D.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t D = D.toScheme.basicOpen (SchemeNorm.Construction.SchemeNormOpen.norm s' a) := by
  ext x
  change D.ι x ∈ Invariant.Construction.InvariantCore.core s t D ↔
    x ∈ D.toScheme.basicOpen (SchemeNorm.Construction.SchemeNormOpen.norm s' a)
  rw [Invariant.Construction.InvariantCore.mem_core, SchemeNorm.Construction.SchemeNormOpen.mem_basicOpen_norm s' b]
  constructor
  · intro h y hy
    rw [← ha]
    apply h (t (j y))
    refine ⟨j y, ?_, rfl⟩
    exact (congrArg (fun f => f y) hs.w).symm.trans (congrArg D.ι hy)
  · intro h y hy
    obtain ⟨r, hr, hr'⟩ := hy
    obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback hs x r hr.symm
    have hm := h z hz
    rw [← ha] at hm
    change t (j z) ∈ D at hm
    simpa only [hz', hr'] using hm

/-- The invariant core is affine when its pullback to the containing affine
open is the norm open constructed above. -/
theorem isAffineOpen_core (e : CategoryTheory.EquivalenceRelation s t)
    (D : X.Opens) [IsAffine D] [IsAffine Y]
    (j : Y ⟶ R) (s' : Y ⟶ D.toScheme) (hs : IsPullback s' j D.ι s)
    {ι : Type v} [Fintype ι]
    (b : letI := s'.appTop.hom.toAlgebra; Module.Basis ι Γ(D, ⊤) Γ(Y, ⊤))
    (a : Γ(Y, ⊤)) (ha : (j ≫ t) ⁻¹ᵁ D = Y.basicOpen a) :
    IsAffineOpen (Invariant.Construction.InvariantCore.core s t D) := by
  have he : D.ι ''ᵁ (D.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t D) = Invariant.Construction.InvariantCore.core s t D := by
    ext x
    change (∃ y, D.ι y ∈ Invariant.Construction.InvariantCore.core s t D ∧ D.ι y = x) ↔
      x ∈ Invariant.Construction.InvariantCore.core s t D
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Invariant.Construction.InvariantCore.core_le s t e D hx⟩, hx, rfl⟩
  rw [← he, preimage_core_eq_norm D j s' hs b a ha]
  rw [Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion]
  exact (isAffineOpen_top D.toScheme).basicOpen _

/-- Starting with an affine neighborhood of an entire finite orbit, choose
a smaller affine open on which a target-valued section detects its own
complement. The source norm can therefore make this open invariant. -/
theorem exists_norm_data (e : CategoryTheory.EquivalenceRelation s t)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U)
    (hUx : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U) :
    ∃ D : X.Opens, IsAffineOpen D ∧ D ≤ U ∧
      (∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ D) ∧
      ∃ a : Γ((s ⁻¹ᵁ D).toScheme, ⊤),
        ((s ⁻¹ᵁ D).ι ≫ t) ⁻¹ᵁ D = (s ⁻¹ᵁ D).toScheme.basicOpen a := by
  let : IsAffine U := hU
  let F : Set U := {y | Invariant.Construction.InvariantCore.Related s t x (U.ι y)}
  have hF : F.Finite := by
    change (U.ι ⁻¹' {y | Invariant.Construction.InvariantCore.Related s t x y}).Finite
    exact (Invariant.Construction.InvariantCore.finite_orbit s t x).preimage
      (f := U.ι) Subtype.val_injective.injOn
  have hFW : F ⊆ U.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t U := fun _ hy =>
    Invariant.Construction.InvariantCore.orbit_subset_core s t e U x hUx _ hy
  obtain ⟨f, hfF, hfW⟩ := AffineNeighborhoodOpen.Construction.AffineNeighborhood.exists_basicOpen_scheme U.toScheme F hF
    (U.ι ⁻¹ᵁ Invariant.Construction.InvariantCore.core s t U) hFW
  let D : X.Opens := U.ι ''ᵁ U.toScheme.basicOpen f
  have hD : IsAffineOpen D :=
    ((isAffineOpen_top U.toScheme).basicOpen f).image_of_isOpenImmersion U.ι
  have hDW : D ≤ Invariant.Construction.InvariantCore.core s t U := by
    rintro y ⟨z, hz, rfl⟩
    exact hfW hz
  have hDx : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ D := by
    intro y hy
    exact ⟨⟨y, hUx y hy⟩, hfF hy, rfl⟩
  have htU : s ⁻¹ᵁ D ≤ t ⁻¹ᵁ U := by
    intro r hr
    exact (Invariant.Construction.InvariantCore.mem_core s t U (s r)).mp (hDW hr) (t r) ⟨r, rfl, rfl⟩
  let g : (s ⁻¹ᵁ D).toScheme ⟶ U.toScheme := t.resLE U (s ⁻¹ᵁ D) htU
  refine ⟨D, hD, hDW.trans (Invariant.Construction.InvariantCore.core_le s t e U), hDx, g.appTop f, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι t htU, Scheme.Hom.comp_preimage,
    U.ι.preimage_image_eq, Scheme.preimage_basicOpen_top]

/-- A basis for the finite relation source on affine opens upgrades the
preceding construction to an invariant affine neighborhood of the orbit. -/
theorem exists_invariant_affine (e : CategoryTheory.EquivalenceRelation s t)
    (x : X) (U : X.Opens) (hU : IsAffineOpen U)
    (hUx : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U)
    (hb : ∀ (D : X.Opens), IsAffineOpen D → D ≤ U →
      ∃ n : ℕ, letI := (s ∣_ D).appTop.hom.toAlgebra;
        Nonempty (Module.Basis (Fin n) Γ(D.toScheme, ⊤) Γ((s ⁻¹ᵁ D).toScheme, ⊤))) :
    ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W ∧
      ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ W := by
  obtain ⟨D, hD, hDU, hDx, a, ha⟩ := exists_norm_data e x U hU hUx
  let : IsAffine D := hD
  have : IsFinite (s ∣_ D) := inferInstance
  have : IsAffine (s ⁻¹ᵁ D).toScheme := isAffine_of_isAffineHom (s ∣_ D)
  obtain ⟨n, ⟨b⟩⟩ := hb D hD hDU
  refine ⟨Invariant.Construction.InvariantCore.core s t D, ?_, (Invariant.Construction.InvariantCore.core_le s t e D).trans hDU,
    Invariant.Construction.InvariantCore.core_invariant s t e D, Invariant.Construction.InvariantCore.orbit_subset_core s t e D x hDx⟩
  exact isAffineOpen_core e D (s ⁻¹ᵁ D).ι (s ∣_ D)
    (isPullback_morphismRestrict s D) b a ha

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineEq.Construction.InvariantAffine
