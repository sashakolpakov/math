import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PresentationPrimeLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Target Prime Spreading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.TargetPrimeSpreading

noncomputable section

/-! A point of a scheme of finite type over a Noetherian affine base,
valued in an arbitrary prime localization, spreads to a principal open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {B A : Type u} [CommRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [LocallyOfFiniteType f]
variable (p : Ideal A) [p.IsPrime]

theorem spread_prime_point_over_noetherian_affine
    (g : Spec (.of (Localization.AtPrime p)) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap A (Localization.AtPrime p)).comp (algebraMap B A)))) :
    ∃ (s : A) (hs : s ∉ p) (j : Spec (.of (Localization.Away s)) ⟶ X),
      Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p s hs)) ≫ j = g ∧
      j ≫ f = Spec.map (CommRingCat.ofHom
        ((algebraMap A (Localization.Away s)).comp (algebraMap B A))) := by
  let C := X.affineOpenCover
  obtain ⟨i, gp, hgp⟩ := Local.RingPointOpenLift.localRingPoint_lift_openCover C.openCover g
  change C.I₀ at i
  let T : Type u := C.X i
  let c : Spec (.of T) ⟶ X := C.f i
  change Spec (.of (Localization.AtPrime p)) ⟶ Spec (.of T) at gp
  change gp ≫ c = g at hgp
  let β : B →+* T := (Spec.preimage (c ≫ f)).hom
  let : Algebra B T := β.toAlgebra
  have hβ : Spec.map (CommRingCat.ofHom β) = c ≫ f := Spec.map_preimage _
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom β)) := by
    rw [hβ]
    exact inferInstanceAs (LocallyOfFiniteType (C.f i ≫ f))
  have hβft : β.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  let : Algebra.FiniteType B T := hβft
  let : Algebra.FinitePresentation B T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let φ : T →+* Localization.AtPrime p := (Spec.preimage gp).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = gp := Spec.map_preimage _
  have hφβ : φ.comp β = (algebraMap A (Localization.AtPrime p)).comp (algebraMap B A) := by
    have h : CommRingCat.ofHom (φ.comp β) = CommRingCat.ofHom
        ((algebraMap A (Localization.AtPrime p)).comp (algebraMap B A)) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, hβ, ← Category.assoc, hgp]
      exact hg
    exact congrArg CommRingCat.Hom.hom h
  obtain ⟨s, hs, k, hkB, hk⟩ := Finite.PresentationPrimeLift.finitePresentation_prime_localization_lift T p φ
    (fun b => RingHom.congr_fun hφβ b)
  refine ⟨s, hs, Spec.map (CommRingCat.ofHom k) ≫ c, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((Principal.PrimeLocalization.principalToPrimeMap p s hs).comp k)) ≫ c = g
    rw [hk, hφ]
    exact hgp
  · rw [Category.assoc, ← hβ, ← Spec.map_comp]
    have he : k.comp β = (algebraMap A (Localization.Away s)).comp (algebraMap B A) := RingHom.ext hkB
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.TargetPrimeSpreading
