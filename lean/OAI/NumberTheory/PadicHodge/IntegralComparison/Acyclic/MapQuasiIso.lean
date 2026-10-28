import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.PositiveNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Map Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.MapQuasiIso

noncomputable section

/-!
# IntegralComparison: an augmented comparison between actual acyclic resolutions remains a quasi-isomorphism on sections
-/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {K L : CochainComplex C ℕ} {Z W : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) (κ : (CochainComplex.single₀ C).obj W ⟶ L)
  [QuasiIso ι] [QuasiIso κ]
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ C).map f ≫ κ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "M" => CategoryTheory.Functor.map
  (CategoryTheory.Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) φ
local notation "aK" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "aL" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X L κ

include hφ

omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation : aK ≫ M = (CochainComplex.single₀ _).map ((F).map f) ≫ aL := by
  apply (CochainComplex.fromSingle₀Equiv (Resolution.Comparison.complex R X L) ((F).obj Z)).injective
  apply Subtype.ext
  have h := Augmented.ResolutionCycleMaps.augmentation φ ι κ f hφ
  have hm : (F).map (Augmented.ResolutionCycles.augmentation K ι) ≫ (F).map (φ.f 0) =
      (F).map f ≫ (F).map (Augmented.ResolutionCycles.augmentation L κ) := by
    rw [← (F).map_comp, ← h, (F).map_comp]
  exact (congrArg (fun a => a ≫ (F).map (φ.f 0)) (ResolutionZero.Comparison.augmentation_zero R X K ι)).trans
    (hm.trans (congrArg₂ (fun a b => a ≫ b)
      (CochainComplex.single₀_map_f_zero ((F).map f)).symm
      (ResolutionZero.Comparison.augmentation_zero R X L κ).symm))

theorem zero [IsIso f] : QuasiIsoAt M 0 := by
  have hl : QuasiIsoAt ((CochainComplex.single₀ (ModuleCat.{z} R)).map ((F).map f) ≫ aL) 0 :=
    inferInstance
  have : QuasiIsoAt (aK ≫ M) 0 := (augmentation R X ι κ φ f hφ).symm ▸ hl
  exact quasiIsoAt_of_comp_left aK M 0

variable (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} X (L.X a) (q + 1)))

include hK hL

theorem positive [IsIso f] (n : ℕ) : QuasiIsoAt M (n + 1) := by
  let eK : (((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology (n + 1) ≅
      ModuleCat.of R (Ext.{z} X Z (n + 1)) :=
    Resolution.Comparison.positiveHomologyIso R X K ι hK n
  let eL : (((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj L).homology (n + 1) ≅
      ModuleCat.of R (Ext.{z} X W (n + 1)) :=
    Resolution.Comparison.positiveHomologyIso R X L κ hL n
  let b : ModuleCat.of R (Ext.{z} X Z (n + 1)) ≅ ModuleCat.of R (Ext.{z} X W (n + 1)) :=
    (IntegralComparison.Ext.ModuleFunctor.functor R X (n + 1)).mapIso (asIso f)
  have hn : HomologicalComplex.homologyMap M (n + 1) ≫ eL.hom = eK.hom ≫ b.hom :=
    PositiveNaturality.naturality R X ι κ hK hL φ f hφ n
  have : IsIso (HomologicalComplex.homologyMap M (n + 1) ≫ eL.hom) :=
    hn.symm ▸ (inferInstance : IsIso (eK.hom ≫ b.hom))
  apply (quasiIsoAt_iff_isIso_homologyMap M (n + 1)).mpr
  exact IsIso.of_isIso_comp_right _ eL.hom

theorem quasiIso [IsIso f] : QuasiIso M := ⟨fun n => by
  cases n with
  | zero => exact MapQuasiIso.zero R X ι κ φ f hφ
  | succ n => exact positive R X ι κ φ f hφ hK hL n⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.MapQuasiIso
