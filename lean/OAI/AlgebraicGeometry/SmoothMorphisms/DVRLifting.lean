import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # DVR Lifting -/

namespace OAI.AlgebraicGeometry.SmoothMorphisms.DVRLifting

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The affine lifting step, using formal smoothness and adic completeness. -/
theorem lift_ring_point
    (R A : Type u) [CommRing R] [IsLocalRing R] [CommRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (φ : R →+* A) (hφ : φ.Smooth)
    (p : A →+* IsLocalRing.ResidueField R)
    (hp : p.comp φ = IsLocalRing.residue R) :
    ∃ q : A →+* R, q.comp φ = RingHom.id R ∧
      (IsLocalRing.residue R).comp q = p := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra.Smooth R A := hφ
  let p' : A →ₐ[R] R ⧸ IsLocalRing.maximalIdeal R :=
    { p with commutes' := fun r => RingHom.congr_fun hp r }
  obtain ⟨q, hq⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete p'
  refine ⟨q.toRingHom, ?_, ?_⟩
  · ext r
    exact q.commutes r
  · exact congrArg AlgHom.toRingHom hq

/-- Lifting for an affine smooth scheme. -/
theorem lift_affine_point
    (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (A : CommRingCat.{u})
    (f : Spec A ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec A)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ Spec A,
      s ≫ f = 𝟙 (Spec (CommRingCat.of R)) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = x := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨p, rfl⟩ := Spec.map_surjective x
  have hφ : φ.hom.Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp inferInstance
  have hp : φ ≫ p = CommRingCat.ofHom (IsLocalRing.residue R) :=
    Spec.map_injective (by simpa only [Spec.map_comp] using hx)
  obtain ⟨q, hq, hred⟩ := lift_ring_point R A φ.hom hφ p.hom
    (congrArg CommRingCat.Hom.hom hp)
  refine ⟨Spec.map (CommRingCat.ofHom q), ?_, ?_⟩
  · rw [← Spec.map_comp, Spec.map_eq_id]
    exact CommRingCat.hom_ext hq
  · rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hred)

/-- DVRLifting: a rational point of the special fiber of a smooth scheme over
a complete DVR lifts to a section over the DVR. -/
theorem lift_special_fiber_point
    (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx : x ≫ f =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X,
      s ≫ f = 𝟙 (Spec (CommRingCat.of R)) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = x := by
  obtain ⟨A, i, hi, y, hy⟩ := Scheme.exists_Spec_apply_eq (x default)
  have hrange : Set.range x ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    refine ⟨y, ?_⟩
    simpa only [Subsingleton.elim z default] using hy
  let x' := IsOpenImmersion.lift i x hrange
  have hx' : x' ≫ i = x := IsOpenImmersion.lift_fac i x hrange
  have hxi : x' ≫ (i ≫ f) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [← Category.assoc, hx', hx]
  obtain ⟨s, hs, hred⟩ := lift_affine_point R A (i ≫ f) x' hxi
  refine ⟨s ≫ i, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred, hx']

end OAI.AlgebraicGeometry.SmoothMorphisms.DVRLifting
