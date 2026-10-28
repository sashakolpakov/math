import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoPresheaf
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Iso Sheaf Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSheafGluing

noncomputable section

/-! Isomorphisms glue whenever the two maps and the two endomorphism presheaves satisfy descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (M N : X.Modules) (T : Over X) (R : Presieve T)

theorem moduleMap_comp_eq_id_of_local
    (hM : Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf M M) R)
    (φ : (Scheme.Modules.pullback T.hom).obj M ⟶ (Scheme.Modules.pullback T.hom).obj N)
    (ψ : (Scheme.Modules.pullback T.hom).obj N ⟶ (Scheme.Modules.pullback T.hom).obj M)
    (h : ∀ {Y : Over X} (f : Y ⟶ T), R f →
      MapSlicePullback.moduleMapPullbackAlong f φ ≫ MapSlicePullback.moduleMapPullbackAlong f ψ = 𝟙 _) : φ ≫ ψ = 𝟙 _ := by
  apply hM.ext
  intro Y f hf
  change MapSlicePullback.moduleMapPullbackAlong f (φ ≫ ψ) = MapSlicePullback.moduleMapPullbackAlong f (𝟙 _)
  rw [MapSliceComposition.moduleMapPullbackAlong_map_comp, IsoSlicePullback.moduleMapPullbackAlong_map_id]
  exact h f hf

theorem moduleIsoFamily_hom_inv
    (hM : Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf M M) R)
    (s : Presieve.FamilyOfElements (IsoPresheaf.moduleIsoPresheaf M N) R)
    (φ : (HomPresheaf.moduleHomPresheaf M N).obj (.op T)) (ψ : (HomPresheaf.moduleHomPresheaf N M).obj (.op T))
    (hφ : (s.map (IsoPresheaf.moduleIsoHom M N)).IsAmalgamation φ)
    (hψ : (s.map (IsoPresheaf.moduleIsoInv M N)).IsAmalgamation ψ) : φ ≫ ψ = 𝟙 _ := by
  apply moduleMap_comp_eq_id_of_local M N T R hM
  intro Y f hf
  have hφf : MapSlicePullback.moduleMapPullbackAlong f φ = (s f hf).hom := hφ f hf
  have hψf : MapSlicePullback.moduleMapPullbackAlong f ψ = (s f hf).inv := hψ f hf
  exact (congrArg₂ (fun a b => a ≫ b) hφf hψf).trans (s f hf).hom_inv_id

theorem moduleIsoFamily_inv_hom
    (hN : Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf N N) R)
    (s : Presieve.FamilyOfElements (IsoPresheaf.moduleIsoPresheaf M N) R)
    (φ : (HomPresheaf.moduleHomPresheaf M N).obj (.op T)) (ψ : (HomPresheaf.moduleHomPresheaf N M).obj (.op T))
    (hφ : (s.map (IsoPresheaf.moduleIsoHom M N)).IsAmalgamation φ)
    (hψ : (s.map (IsoPresheaf.moduleIsoInv M N)).IsAmalgamation ψ) : ψ ≫ φ = 𝟙 _ := by
  apply moduleMap_comp_eq_id_of_local N M T R hN
  intro Y f hf
  have hφf : MapSlicePullback.moduleMapPullbackAlong f φ = (s f hf).hom := hφ f hf
  have hψf : MapSlicePullback.moduleMapPullbackAlong f ψ = (s f hf).inv := hψ f hf
  exact (congrArg₂ (fun a b => a ≫ b) hψf hφf).trans (s f hf).inv_hom_id

theorem moduleIso_isSheafFor
    (hMN : Presieve.IsSheafFor (HomPresheaf.moduleHomPresheaf M N) R)
    (hNM : Presieve.IsSheafFor (HomPresheaf.moduleHomPresheaf N M) R)
    (hMM : Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf M M) R)
    (hNN : Presieve.IsSeparatedFor (HomPresheaf.moduleHomPresheaf N N) R) :
    Presieve.IsSheafFor (IsoPresheaf.moduleIsoPresheaf M N) R := by
  intro s hs
  obtain ⟨φ, hφ, hφu⟩ := hMN (s.map (IsoPresheaf.moduleIsoHom M N)) (hs.map (IsoPresheaf.moduleIsoHom M N))
  obtain ⟨ψ, hψ, _⟩ := hNM (s.map (IsoPresheaf.moduleIsoInv M N)) (hs.map (IsoPresheaf.moduleIsoInv M N))
  change (Scheme.Modules.pullback T.hom).obj M ⟶ (Scheme.Modules.pullback T.hom).obj N at φ
  change (Scheme.Modules.pullback T.hom).obj N ⟶ (Scheme.Modules.pullback T.hom).obj M at ψ
  have hφψ := moduleIsoFamily_hom_inv M N T R hMM s φ ψ hφ hψ
  have hψφ := moduleIsoFamily_inv_hom M N T R hNN s φ ψ hφ hψ
  let e : (Scheme.Modules.pullback T.hom).obj M ≅ (Scheme.Modules.pullback T.hom).obj N :=
    ⟨φ, ψ, hφψ, hψφ⟩
  refine ⟨e, ?_, ?_⟩
  · intro Y f hf
    apply Iso.ext
    exact hφ f hf
  · intro e' he'
    apply Iso.ext
    apply hφu
    intro Y f hf
    exact congrArg Iso.hom (he' f hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSheafGluing
