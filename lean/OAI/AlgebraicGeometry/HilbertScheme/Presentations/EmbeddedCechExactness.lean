import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechDifferential
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Embedded Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechExactness.ProjectiveCech

noncomputable section

/-! Deleting complementary zero variables preserves and reflects Čech exactness. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w} [LinearOrder σ] [LinearOrder τ]
variable (R : Type u) [CommRing R] (e : σ ↪o τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) =
  (MvPolynomial.killCompl e.injective).toRingHom)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

include he in
theorem embedded_moduleCechExactAt_iff (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := τ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  let E := EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv R e.toEmbedding he M
  have hd (x : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
      E (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M x) = ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (E x) :=
    EmbeddedCechDifferential.ProjectiveCech.embeddedModuleCechEquiv_differential R e he M x
  have hh (x : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (E x) ↔ ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d x :=
    EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv_homogeneous R e.toEmbedding he M ℳ d x
  have hc (r : ℕ) (x : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M r (E x) ↔ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M r x :=
    EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv_card R e.toEmbedding he M r x
  constructor
  · intro h y hy hyc hyd
    obtain ⟨x, rfl⟩ := E.surjective y
    have hxd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M x = 0 := by
      apply E.injective
      rw [hd, map_zero, hyd]
    obtain ⟨a, ha, hac, had⟩ := h x ((hh x).mp hy) ((hc q x).mp hyc) hxd
    refine ⟨E a, (hh a).mpr ha, (hc (q - 1) a).mpr hac, ?_⟩
    rw [← hd, had]
  · intro h x hx hxc hxd
    have hyd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (E x) = 0 := by
      rw [← hd, hxd, map_zero]
    obtain ⟨a, ha, hac, had⟩ := h (E x) ((hh x).mpr hx) ((hc q x).mpr hxc) hyd
    obtain ⟨b, rfl⟩ := E.surjective a
    refine ⟨b, (hh b).mp ha, (hc (q - 1) b).mp hac, ?_⟩
    apply E.injective
    rw [hd, had]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechExactness.ProjectiveCech
