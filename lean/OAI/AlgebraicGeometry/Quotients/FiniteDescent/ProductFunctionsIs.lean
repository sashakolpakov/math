import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Product Functions Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFunctionsIs.Construction.ProductFunctions

noncomputable section

/-! Universal constancy of functions on a proper integral scheme over an
algebraically closed field, including nonreduced base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
variable [IsIntegral X] [IsProper f]

theorem isIso_appTop : IsIso f.appTop := by
  have h : IsIso (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (IsAlgClosed.ringHom_bijective_of_isIntegral
        (ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f).hom (ProperIntegral.Construction.ProperIntegralFunctions.isIntegral f))
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) := h
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv f.appTop

theorem isIso_app_affine (U : Y.Opens) (hU : IsAffineOpen U) :
    IsIso ((pullback.snd f g).app U) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  let H := IsPullback.of_hasPullback f g
  have hUX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := le_rfl
  have hUY : U ≤ g ⁻¹ᵁ ⊤ := le_top
  have hUV : pullback.snd f g ⁻¹ᵁ U =
      pullback.fst f g ⁻¹ᵁ ⊤ ⊓ pullback.snd f g ⁻¹ᵁ U := by simp
  have hq := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUY hUX hUV
    (isAffineOpen_top (Spec (.of K))) hU isCompact_univ isQuasiSeparated_univ
  have hp := (isIso_pushoutSection_iff H hUY hUX hUV).mp hq
  have : IsIso (f.appLE ⊤ ⊤ hUX) := by
    change IsIso (f.appLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact isIso_appTop f
  have h := hp.isIso_inr_of_isIso
  change IsIso ((pullback.snd f g).appLE U (pullback.snd f g ⁻¹ᵁ U) le_rfl) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

theorem isIso_unit :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (pullback.snd f g).toRingCatSheafHom) := by
  let q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶
      (Scheme.Modules.pushforward (pullback.snd f g)).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) :=
    SheafOfModules.unitToPushforwardObjUnit (pullback.snd f g).toRingCatSheafHom
  have : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map q) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : Y.affineOpens => U.1)
      (by simpa only [Subtype.range_val] using Y.isBasis_affineOpens)
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have := isIso_app_affine f g U.1 U.2
    exact (ConcreteCategory.isIso_iff_bijective ((pullback.snd f g).app U.1)).mp this
  have : IsIso ((Scheme.Modules.toPresheaf Y).map q) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map q)))
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf Y)

def iso : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅
    (Scheme.Modules.pushforward (pullback.snd f g)).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) :=
  @asIso _ _ _ _ _ (isIso_unit f g)

theorem isIso_app (U : Y.Opens) : IsIso ((pullback.snd f g).app U) := by
  have h := (ConcreteCategory.isIso_iff_bijective ((iso f g).hom.app U)).mp inferInstance
  exact (ConcreteCategory.isIso_iff_bijective ((pullback.snd f g).app U)).mpr h

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductFunctionsIs.Construction.ProductFunctions
