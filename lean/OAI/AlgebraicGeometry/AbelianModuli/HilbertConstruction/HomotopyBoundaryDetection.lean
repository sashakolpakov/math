import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary

/-! # Homotopy Boundary Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomotopyBoundaryDetection.CechBoundaryTransport

noncomputable section

/-! Boundary detection survives comparison squares that commute up to
homotopy. Finite projective Cech models therefore need only homotopy
comparisons with the original restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

section

variable {R : Type u} [CommRing R]
variable {S T : ShortComplex (ModuleCat.{u} R)}

theorem boundary_of_homotopy {a b : S ⟶ T} (h : ShortComplex.Homotopy a b)
    (z : S.X₂) (hz : S.g z = 0) (hb : b.τ₂ z ∈ T.f.hom.range) :
    a.τ₂ z ∈ T.f.hom.range := by
  obtain ⟨x, hx⟩ := hb
  refine ⟨h.h₁ z + x, ?_⟩
  have he := ConcreteCategory.congr_hom h.comm₂ z
  change a.τ₂ z = h.h₂ (S.g z) + T.f (h.h₁ z) + b.τ₂ z at he
  simpa only [hz, map_zero, zero_add, map_add, hx] using he.symm

theorem jointly_of_homotopy_square
    {T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}
    (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (s₁ : T ⟶ Q₁) (s₂ : T ⟶ Q₂)
    (e : S ⟶ T) [ShortComplex.QuasiIso e] (a₁ : T₁ ⟶ Q₁) (a₂ : T₂ ⟶ Q₂)
    (h₁ : ShortComplex.Homotopy (e ≫ s₁) (r₁ ≫ a₁))
    (h₂ : ShortComplex.Homotopy (e ≫ s₂) (r₂ ≫ a₂))
    (hd : Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects s₁ s₂) :
    Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects r₁ r₂ := by
  intro z hz hb₁ hb₂
  apply Quotients.FiniteDescent.HomologyInjective.Construction.HomologyInjectiveCriterion.boundary e
    ((ModuleCat.mono_iff_injective _).mp inferInstance) z hz
  apply hd (e.τ₂ z) (Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.cycle e z hz)
  · exact boundary_of_homotopy h₁ z hz
      (Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.boundary a₁ (r₁.τ₂ z) hb₁)
  · exact boundary_of_homotopy h₂ z hz
      (Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.boundary a₂ (r₂.τ₂ z) hb₂)

end

variable {R K : Type u} [CommRing R] [CommRing K]
variable {S T T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}

theorem jointly_of_iso_middle_map (F : ModuleCat.{u} R ⥤ ModuleCat.{u} K)
    [F.PreservesZeroMorphisms]
    (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (s₁ : T ⟶ Q₁) (s₂ : T ⟶ Q₂)
    (e : S ≅ T) (a₁ : T₁ ⟶ Q₁) (a₂ : T₂ ⟶ Q₂)
    (h₁ : r₁.τ₂ ≫ a₁.τ₂ = e.hom.τ₂ ≫ s₁.τ₂)
    (h₂ : r₂.τ₂ ≫ a₂.τ₂ = e.hom.τ₂ ≫ s₂.τ₂)
    (hd : Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      (F.mapShortComplex.map s₁) (F.mapShortComplex.map s₂)) :
    Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      (F.mapShortComplex.map r₁) (F.mapShortComplex.map r₂) := by
  apply Quotients.FiniteDescent.CechBoundary.Construction.CechBoundaryTransport.jointly_of_iso_middle
    (F.mapShortComplex.map r₁) (F.mapShortComplex.map r₂)
    (F.mapShortComplex.map s₁) (F.mapShortComplex.map s₂)
    (F.mapShortComplex.mapIso e) (F.mapShortComplex.map a₁)
    (F.mapShortComplex.map a₂) _ _ hd
  · intro z
    exact ConcreteCategory.congr_hom
      ((F.map_comp _ _).symm.trans ((congrArg F.map h₁).trans (F.map_comp _ _))) z
  · intro z
    exact ConcreteCategory.congr_hom
      ((F.map_comp _ _).symm.trans ((congrArg F.map h₂).trans (F.map_comp _ _))) z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomotopyBoundaryDetection.CechBoundaryTransport
