import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Quotient Induction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.QuotientInduction

noncomputable section

/-! Noetherian induction formulated with arbitrary surjective presentations
of quotient rings, so that canonical quotient types need not be changed. -/

open _root_.CategoryTheory

universe u

theorem noetherian_quotient_induction (R : CommRingCat.{u}) [IsNoetherianRing R]
    (P : CommRingCat.{u} → Prop)
    (hstep : ∀ (A : CommRingCat.{u}) [IsNoetherianRing A],
      (∀ (B : CommRingCat.{u}) (ψ : A ⟶ B), Function.Surjective ψ →
        RingHom.ker ψ.hom ≠ ⊥ → P B) → P A) : P R := by
  have h (J : Ideal R) : ∀ (A : CommRingCat.{u}) (φ : R ⟶ A),
      Function.Surjective φ → RingHom.ker φ.hom = J → P A := by
    induction J using WellFoundedGT.induction with
    | ind J ih =>
      intro A φ hφ hker
      let : IsNoetherianRing A := isNoetherianRing_of_surjective R A φ.hom hφ
      apply hstep A
      intro B ψ hψ hψker
      have hle : RingHom.ker φ.hom ≤ RingHom.ker (φ ≫ ψ).hom := by
        intro r hr
        change ψ (φ r) = 0
        rw [show φ r = 0 from hr, map_zero]
      have hne : RingHom.ker φ.hom ≠ RingHom.ker (φ ≫ ψ).hom := by
        intro he
        apply hψker
        apply Ideal.comap_injective_of_surjective φ.hom hφ
        change (RingHom.ker ψ.hom).comap φ.hom = RingHom.ker φ.hom
        rw [RingHom.comap_ker]
        exact he.symm
      exact ih (RingHom.ker (φ ≫ ψ).hom) (hker ▸ lt_of_le_of_ne hle hne)
        B (φ ≫ ψ) (hψ.comp hφ) rfl
  exact h (RingHom.ker (CommRingCat.Hom.hom (𝟙 R))) R (𝟙 R) Function.surjective_id rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.QuotientInduction
