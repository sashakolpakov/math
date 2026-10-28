import Mathlib

/-! # Module Homology Maps -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps

noncomputable section

/-!
# Explicit maps on module homology

Maps on cycle quotients are identified with the actual categorical
homology maps through checked left-homology map data.
-/

universe u v

open _root_.CategoryTheory

variable {R : Type u} [CommRing R]
  {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)

def cycleMap : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (f.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (fun x => by
    change T.g (f.τ₂ x) = 0
    have h := congrArg (fun h : S.X₂ ⟶ T.X₃ => h x) f.comm₂₃
    change T.g (f.τ₂ x) = f.τ₃ (S.g x) at h
    have hx : S.g x = 0 := x.property
    rw [hx, map_zero] at h
    exact h)

theorem cycleMap_toCycles :
    (cycleMap f).comp S.moduleCatToCycles = T.moduleCatToCycles.comp f.τ₁.hom := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (congrArg (fun h : S.X₁ ⟶ T.X₂ => h x) f.comm₁₂).symm

theorem cycleMap_preserves_boundaries :
    LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap (cycleMap f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.τ₁ x, (DFunLike.congr_fun (cycleMap_toCycles f) x).symm⟩

def quotientMap :
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[R]
      (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) :=
  (LinearMap.range S.moduleCatToCycles).mapQ (LinearMap.range T.moduleCatToCycles)
    (cycleMap f) (cycleMap_preserves_boundaries f)

def mapData : ShortComplex.LeftHomologyMapData f
    S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (cycleMap f)
  φH := ModuleCat.ofHom (quotientMap f)
  commi := rfl
  commf' := ModuleCat.hom_ext (cycleMap_toCycles f)
  commπ := rfl

theorem homologyMap_natural :
    ShortComplex.homologyMap f ≫ T.moduleCatHomologyIso.hom =
      S.moduleCatHomologyIso.hom ≫ ModuleCat.ofHom (quotientMap f) :=
  (mapData f).homologyMap_comm

theorem quasiIso_iff_bijective : ShortComplex.QuasiIso f ↔ Function.Bijective (quotientMap f) := by
  rw [(mapData f).quasiIso_iff]
  exact ConcreteCategory.isIso_iff_bijective _

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
