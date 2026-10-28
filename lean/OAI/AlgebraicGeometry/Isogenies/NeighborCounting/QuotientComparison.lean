import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientAction

/-! # Quotient Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

noncomputable section

/-!
Canonical comparisons of actual isogeny quotients. Equal scheme kernels
give an isomorphism by fpqc descent. The action and ordered full marking
are then proved to agree from their constructions, not assumed compatible.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power.Construction

variable {S : Scheme.{u}} {d : ℕ}
variable {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}

local instance isogeny_epi (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) : Epi f.hom := by
  have : EffectiveEpi f.hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc f.hom
  infer_instance

def SameKernel (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C) : Prop :=
  ∀ (T : Over S) (a : T ⟶ A.scheme), a ≫ f.hom = 1 ↔ a ≫ g.hom = 1

theorem quotient_comparison_exists
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) :
    ∃ e : B.scheme ≅ C.scheme, IsMonHom e.hom ∧ f.hom ≫ e.hom = g.hom := by
  obtain ⟨b, ⟨hbHom, hb⟩, _⟩ := Picard.PoincareBundle.Epi.Construction.fpqc_group_hom_descent f.hom g.hom
    (fun T a ha => (hk T a).mp ha)
  obtain ⟨c, ⟨hcHom, hc⟩, _⟩ := Picard.PoincareBundle.Epi.Construction.fpqc_group_hom_descent g.hom f.hom
    (fun T a ha => (hk T a).mpr ha)
  have hbc : b ≫ c = 𝟙 B.scheme := by
    apply (cancel_epi f.hom).mp
    rw [← Category.assoc, hb, hc, Category.comp_id]
  have hcb : c ≫ b = 𝟙 C.scheme := by
    apply (cancel_epi g.hom).mp
    rw [← Category.assoc, hc, hb, Category.comp_id]
  exact ⟨⟨b, c, hbc, hcb⟩, hbHom, hb⟩

def quotientIso
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) : B.scheme ≅ C.scheme :=
  (quotient_comparison_exists f g hk).choose

instance quotientIso_isMonHom
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) : IsMonHom (quotientIso f g hk).hom :=
  (quotient_comparison_exists f g hk).choose_spec.1

theorem quotientIso_projection
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) : f.hom ≫ (quotientIso f g hk).hom = g.hom :=
  (quotient_comparison_exists f g hk).choose_spec.2

/-- Every chosen level section is transported through the constructed
quotient comparison. This proves equality of the actual ordered marking. -/
theorem quotientIso_preserves_quotientLevel
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) {n N : ℕ} (hnN : Nat.Coprime n N)
    (hf : ∀ (T : Over S) (a : T ⟶ A.scheme), a ≫ f.hom = 1 → a ^ n = 1)
    (level : A.FullLevel N) (T : (Over S)ᵒᵖ)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor d N S).obj T) :
    ((AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel f hnN hf level).hom.app T c).val ≫ (quotientIso f g hk).hom =
      ((AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel g hnN (fun T a ha => hf T a ((hk T a).mpr ha)) level).hom.app T c).val := by
  rw [AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel_transports, AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel_transports,
    Category.assoc, quotientIso_projection]

/-- The descended integral endomorphism action is also preserved by the
same quotient comparison; its compatibility is proved by cancellation. -/
theorem quotientIso_preserves_quotientAction
    {R : Type v} [CommRing R] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (hk : SameKernel f g) (hf : AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.ActionStableKernel ρ f) (hg : AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.ActionStableKernel ρ g)
    (r : R) :
    (AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.quotientAction ρ f hf).map r ≫ (quotientIso f g hk).hom =
      (quotientIso f g hk).hom ≫ (AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.quotientAction ρ g hg).map r := by
  apply (cancel_epi f.hom).mp
  rw [← Category.assoc, AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.quotientAction_intertwines, Category.assoc,
    quotientIso_projection, ← Category.assoc, quotientIso_projection,
    AbelianScheme.FrobeniusKernel.QuotientActionBase.Construction.quotientAction_intertwines]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
