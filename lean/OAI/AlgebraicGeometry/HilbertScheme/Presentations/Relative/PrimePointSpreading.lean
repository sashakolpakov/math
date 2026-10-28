import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.TargetPrimeSpreading
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Prime Point Spreading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PrimePointSpreading

noncomputable section

/-! Relative scheme points at coefficient primes spread over arbitrary
test rings once the base map factors through a Noetherian affine scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {B A : Type u} [CommRing B] [IsNoetherianRing B]
variable [CommRing A] [Algebra B A]
variable (H : Over S) [LocallyOfFiniteType H.hom]

theorem spread_relative_prime_point
    (c : Spec (.of B) ⟶ S) (a : Spec (.of A) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ c = a)
    (p : Ideal A) [p.IsPrime] (g : Spec (.of (Localization.AtPrime p)) ⟶ H.left)
    (hg : g ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p))) ≫ a) :
    ∃ (s : A) (hs : s ∉ p) (j : Spec (.of (Localization.Away s)) ⟶ H.left),
      Spec.map (CommRingCat.ofHom (Principal.PrimeLocalization.principalToPrimeMap p s hs)) ≫ j = g ∧
      j ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ a := by
  let d : Spec (.of (Localization.AtPrime p)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom ((algebraMap A (Localization.AtPrime p)).comp (algebraMap B A)))
  have hd : d ≫ c = Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p))) ≫ a := by
    rw [← ha, ← Category.assoc, ← Spec.map_comp]
    rfl
  let gp : Spec (.of (Localization.AtPrime p)) ⟶ pullback H.hom c :=
    pullback.lift g d (hg.trans hd.symm)
  have hgp : gp ≫ pullback.snd H.hom c = d := pullback.lift_snd _ _ _
  obtain ⟨s, hs, jp, hjp, hjbase⟩ :=
    Noetherian.TargetPrimeSpreading.spread_prime_point_over_noetherian_affine (pullback.snd H.hom c) p gp hgp
  refine ⟨s, hs, jp ≫ pullback.fst H.hom c, ?_, ?_⟩
  · rw [← Category.assoc, hjp]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hjbase]
    rw [← ha, ← Category.assoc, ← Spec.map_comp]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PrimePointSpreading
