import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Smooth.Basic

/-! # Infinitesimal Lifting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting.Construction

noncomputable section

/-!
Infinitesimal lifting for the finite etale quotient. The lift is obtained
from the actual formally smooth coordinate algebra, so compatibility on
dual-number points is a theorem rather than a premise of the Lie adapter.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A section modulo a nilpotent ideal of an affine etale scheme lifts
to a section. The construction uses the coordinate algebra of the scheme. -/
theorem affine_etale_nilpotent_section
    {C D : Type u} [CommRing C] [CommRing D] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of C)) [Etale p]
    (π : C →+* D) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (x₀ : Spec (CommRingCat.of D) ⟶ X)
    (hx₀ : x₀ ≫ p = Spec.map (CommRingCat.ofHom π)) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X,
      x ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom π) ≫ x = x₀ := by
  let γ : CommRingCat.of C ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)
  let γ₀ : Γ(X, ⊤) ⟶ CommRingCat.of D := Spec.preimage (x₀ ≫ X.isoSpec.hom)
  have hγ : Spec.map γ = X.isoSpec.inv ≫ p := Spec.map_preimage _
  have hγ₀ : Spec.map γ₀ = x₀ ≫ X.isoSpec.hom := Spec.map_preimage _
  have hcompat : γ ≫ γ₀ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hγ, hγ₀]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hx₀
  have : Etale (Spec.map γ) := hγ.symm ▸ inferInstance
  have hEtale : γ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  let : Algebra C Γ(X, ⊤) := γ.hom.toAlgebra
  have : Algebra.Etale C Γ(X, ⊤) := hEtale
  have : Algebra.FormallySmooth C Γ(X, ⊤) := inferInstance
  let : Algebra C D := π.toAlgebra
  let a : Γ(X, ⊤) →ₐ[C] D := {
    toRingHom := γ₀.hom
    commutes' := fun c => congrArg (fun z : CommRingCat.of C ⟶ CommRingCat.of D => z.hom c)
      hcompat }
  let l := Algebra.FormallySmooth.liftOfSurjective a (Algebra.ofId C D) hπ hker
  have hl := Algebra.FormallySmooth.comp_liftOfSurjective a (Algebra.ofId C D) hπ hker
  let L : Γ(X, ⊤) ⟶ CommRingCat.of C := CommRingCat.ofHom l.toRingHom
  have hL : γ ≫ L = 𝟙 (CommRingCat.of C) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext l.commutes
  have hred : L ≫ CommRingCat.ofHom π = γ₀ := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hl
  refine ⟨Spec.map L ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hγ, ← Spec.map_comp, hL, Spec.map_id]
  · apply (cancel_mono X.isoSpec.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Spec.map_comp, hred, hγ₀]

/-- Uniqueness of the infinitesimal section, using formal unramifiedness
of the same actual coordinate algebra. -/
theorem affine_etale_nilpotent_section_unique
    {C D : Type u} [CommRing C] [CommRing D] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of C)) [Etale p]
    (π : C →+* D) (hker : IsNilpotent (RingHom.ker π))
    (x y : Spec (CommRingCat.of C) ⟶ X)
    (hx : x ≫ p = 𝟙 _) (hy : y ≫ p = 𝟙 _)
    (hred : Spec.map (CommRingCat.ofHom π) ≫ x =
      Spec.map (CommRingCat.ofHom π) ≫ y) : x = y := by
  let γ : CommRingCat.of C ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)
  let Lx : Γ(X, ⊤) ⟶ CommRingCat.of C := Spec.preimage (x ≫ X.isoSpec.hom)
  let Ly : Γ(X, ⊤) ⟶ CommRingCat.of C := Spec.preimage (y ≫ X.isoSpec.hom)
  have hγ : Spec.map γ = X.isoSpec.inv ≫ p := Spec.map_preimage _
  have hLx : Spec.map Lx = x ≫ X.isoSpec.hom := Spec.map_preimage _
  have hLy : Spec.map Ly = y ≫ X.isoSpec.hom := Spec.map_preimage _
  have hcx : γ ≫ Lx = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hγ, hLx, Spec.map_id]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hx
  have hcy : γ ≫ Ly = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hγ, hLy, Spec.map_id]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hy
  have : Etale (Spec.map γ) := hγ.symm ▸ inferInstance
  have hEtale : γ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  let : Algebra C Γ(X, ⊤) := γ.hom.toAlgebra
  have : Algebra.Etale C Γ(X, ⊤) := hEtale
  let ax : Γ(X, ⊤) →ₐ[C] C := {
    toRingHom := Lx.hom
    commutes' := fun c => congrArg (fun z : CommRingCat.of C ⟶ CommRingCat.of C => z.hom c) hcx }
  let ay : Γ(X, ⊤) →ₐ[C] C := {
    toRingHom := Ly.hom
    commutes' := fun c => congrArg (fun z : CommRingCat.of C ⟶ CommRingCat.of C => z.hom c) hcy }
  have hr : Lx ≫ CommRingCat.ofHom π = Ly ≫ CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hLx, hLy, ← Category.assoc, ← Category.assoc, hred]
  have he : ax = ay := Algebra.FormallyUnramified.lift_unique_of_ringHom π hker ax ay
    (congrArg (fun z : Γ(X, ⊤) ⟶ CommRingCat.of D => z.hom) hr)
  have heL : Lx = Ly := CommRingCat.hom_ext (congrArg AlgHom.toRingHom he)
  apply (cancel_mono X.isoSpec.hom).mp
  rw [← hLx, ← hLy, heL]

/-- A finite etale morphism lifts a specified infinitesimal test point
through every nilpotent quotient of an affine test scheme. -/
theorem finite_etale_nilpotent_lift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    {C D : Type u} [CommRing C] [CommRing D] (π : C →+* D) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (y : Spec (CommRingCat.of C) ⟶ Y)
    (x₀ : Spec (CommRingCat.of D) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom π) ≫ y) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X,
      x ≫ f = y ∧
      Spec.map (CommRingCat.ofHom π) ≫ x = x₀ := by
  let Z := pullback f y
  let p : Z ⟶ Spec (CommRingCat.of C) := pullback.snd f y
  have : IsFinite p := inferInstance
  have : Etale p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  let a : Spec (CommRingCat.of D) ⟶ Z :=
    pullback.lift x₀ (Spec.map (CommRingCat.ofHom π)) hx₀
  obtain ⟨s, hs, hs₀⟩ := affine_etale_nilpotent_section Z p π hπ hker a (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst f y, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · rw [← Category.assoc, hs₀]
    exact pullback.lift_fst _ _ _

/-- Two infinitesimal lifts through a finite etale morphism coincide. -/
theorem finite_etale_nilpotent_hom_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    {C D : Type u} [CommRing C] [CommRing D]
    (π : C →+* D) (hker : IsNilpotent (RingHom.ker π))
    (x y : Spec (CommRingCat.of C) ⟶ X)
    (hbase : x ≫ f = y ≫ f)
    (hred : Spec.map (CommRingCat.ofHom π) ≫ x =
      Spec.map (CommRingCat.ofHom π) ≫ y) : x = y := by
  let Z := pullback f (x ≫ f)
  let p : Z ⟶ Spec (CommRingCat.of C) := pullback.snd f (x ≫ f)
  have : IsFinite p := inferInstance
  have : Etale p := inferInstance
  have : IsAffine Z := isAffine_of_isAffineHom p
  let a : Spec (CommRingCat.of C) ⟶ Z :=
    pullback.lift x (𝟙 _) (Category.id_comp _).symm
  let b : Spec (CommRingCat.of C) ⟶ Z :=
    pullback.lift y (𝟙 _) (hbase.symm.trans (Category.id_comp _).symm)
  have hab : a = b := affine_etale_nilpotent_section_unique Z p π hker a b
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (by
      apply pullback.hom_ext
      · simpa only [a, b, Category.assoc, pullback.lift_fst] using hred
      · simp only [a, b, Category.assoc, pullback.lift_snd])
  have h := congrArg (fun z => z ≫ pullback.fst f (x ≫ f)) hab
  simpa only [a, b, pullback.lift_fst] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting.Construction
