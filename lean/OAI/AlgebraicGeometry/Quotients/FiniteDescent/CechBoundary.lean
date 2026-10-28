import OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective

/-! # Cech Boundary -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport

noncomputable section

/-! Boundary detection transports through coefficient isomorphisms and
commuting comparison squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R]
variable {S T : ShortComplex (ModuleCat.{u} R)}

theorem cycle (a : S ⟶ T) (z : S.X₂) (hz : S.g z = 0) : T.g (a.τ₂ z) = 0 := by
  exact (ConcreteCategory.congr_hom a.comm₂₃ z).trans
    (by change a.τ₃ (S.g z) = 0; rw [hz, map_zero])

theorem boundary (a : S ⟶ T) (z : S.X₂) (hz : z ∈ S.f.hom.range) :
    a.τ₂ z ∈ T.f.hom.range := by
  obtain ⟨x, hx⟩ := hz
  refine ⟨a.τ₁ x, ?_⟩
  exact (ConcreteCategory.congr_hom a.comm₁₂ x).trans (congrArg a.τ₂ hx)

theorem reflect (e : S ≅ T) (z : S.X₂) (hz : S.g z = 0)
    (hb : e.hom.τ₂ z ∈ T.f.hom.range) : z ∈ S.f.hom.range :=
  HomologyInjective.Construction.HomologyInjectiveCriterion.boundary e.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) z hz hb

def JointlyDetects {T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) : Prop :=
  ∀ z : S.X₂, S.g z = 0 → r₁.τ₂ z ∈ T₁.f.hom.range →
    r₂.τ₂ z ∈ T₂.f.hom.range → z ∈ S.f.hom.range

theorem jointly_of_iso {T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}
    (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (s₁ : T ⟶ Q₁) (s₂ : T ⟶ Q₂)
    (e : S ≅ T) (a₁ : T₁ ⟶ Q₁) (a₂ : T₂ ⟶ Q₂)
    (h₁ : r₁ ≫ a₁ = e.hom ≫ s₁) (h₂ : r₂ ≫ a₂ = e.hom ≫ s₂)
    (hd : JointlyDetects s₁ s₂) : JointlyDetects r₁ r₂ := by
  intro z hz hb₁ hb₂
  apply reflect e z hz
  apply hd (e.hom.τ₂ z) (cycle e.hom z hz)
  · have he := congrArg (fun q : S ⟶ Q₁ => q.τ₂ z) h₁
    exact he ▸ boundary a₁ (r₁.τ₂ z) hb₁
  · have he := congrArg (fun q : S ⟶ Q₂ => q.τ₂ z) h₂
    exact he ▸ boundary a₂ (r₂.τ₂ z) hb₂

theorem jointly_postcompose_isos {T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}
    (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (e₁ : T₁ ≅ Q₁) (e₂ : T₂ ≅ Q₂)
    (hd : JointlyDetects r₁ r₂) : JointlyDetects (r₁ ≫ e₁.hom) (r₂ ≫ e₂.hom) := by
  intro z hz hb₁ hb₂
  exact hd z hz (reflect e₁ (r₁.τ₂ z) (cycle r₁ z hz) hb₁)
    (reflect e₂ (r₂.τ₂ z) (cycle r₂ z hz) hb₂)

theorem jointly_of_iso_middle {T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}
    (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (s₁ : T ⟶ Q₁) (s₂ : T ⟶ Q₂)
    (e : S ≅ T) (a₁ : T₁ ⟶ Q₁) (a₂ : T₂ ⟶ Q₂)
    (h₁ : ∀ z, a₁.τ₂ (r₁.τ₂ z) = s₁.τ₂ (e.hom.τ₂ z))
    (h₂ : ∀ z, a₂.τ₂ (r₂.τ₂ z) = s₂.τ₂ (e.hom.τ₂ z))
    (hd : JointlyDetects s₁ s₂) : JointlyDetects r₁ r₂ := by
  intro z hz hb₁ hb₂
  apply reflect e z hz
  apply hd (e.hom.τ₂ z) (cycle e.hom z hz)
  · rw [← h₁]
    exact boundary a₁ (r₁.τ₂ z) hb₁
  · rw [← h₂]
    exact boundary a₂ (r₂.τ₂ z) hb₂

theorem jointly_precompose {T₁ T₂ : ShortComplex (ModuleCat.{u} R)}
    (a : S ⟶ T) [ShortComplex.QuasiIso a] (r₁ : T ⟶ T₁) (r₂ : T ⟶ T₂)
    (hd : JointlyDetects r₁ r₂) : JointlyDetects (a ≫ r₁) (a ≫ r₂) := by
  intro z hz hb₁ hb₂
  exact HomologyInjective.Construction.HomologyInjectiveCriterion.boundary a
    ((ModuleCat.mono_iff_injective _).mp inferInstance) z hz
    (hd (a.τ₂ z) (cycle a z hz) hb₁ hb₂)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport
