import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs

/-! # Quotient Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientUniqueness

noncomputable section

/-! Equal scheme-theoretic kernels identify actual fpqc group quotients.
Both directions of the comparison are descended, and their inverse and
group laws follow from the quotient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]

/-- Construct the exact group-scheme isomorphism between two quotients
with the same full kernel functor, retaining the actual quotient map. -/
theorem quotient_group_iso_of_same_kernel
    (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    [Flat g.left] [Surjective g.left] [QuasiCompact g.left]
    (hkernel : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 ↔ x ≫ g = 1) :
    ∃ e : B ≅ C, IsMonHom e.hom ∧ f ≫ e.hom = g := by
  have : EffectiveEpi f := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f
  have : EffectiveEpi g := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc g
  obtain ⟨a, ⟨ha, hfa⟩, _⟩ := IsogenyFactorizationIs.IsogenyFactorization.fpqc_group_hom_descent f g
    (fun T x hx => (hkernel T x).mp hx)
  obtain ⟨b, ⟨_, hgb⟩, _⟩ := IsogenyFactorizationIs.IsogenyFactorization.fpqc_group_hom_descent g f
    (fun T x hx => (hkernel T x).mpr hx)
  have hab : a ≫ b = 𝟙 B := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hfa, hgb, Category.comp_id]
  have hba : b ≫ a = 𝟙 C := by
    apply (cancel_epi g).mp
    rw [← Category.assoc, hgb, hfa, Category.comp_id]
  exact ⟨⟨a, b, hab, hba⟩, ha, hfa⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientUniqueness
