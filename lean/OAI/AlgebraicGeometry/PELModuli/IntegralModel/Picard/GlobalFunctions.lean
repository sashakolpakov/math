import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions

noncomputable section

/-! Universal constancy of global functions on a proper integral scheme
over an algebraically closed field, including nonreduced base changes.
This retains the geometric argument of UniversalGlobalSections with
direct proved imports and no Openness statement dependency. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

def globalConstants {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

theorem globalConstants_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (globalConstants f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

theorem isIso_appTop_of_proper_integral
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f] : IsIso f.appTop := by
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact globalConstants_bijective f
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop

theorem isIso_properBaseChange_app_of_isAffineOpen
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsIso ((fst Y X).left.app U) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : QuasiSeparatedSpace X.left := inferInstance
  let H := (IsPullback.of_hasPullback Y.hom X.hom).flip
  have hUX : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ ⊤ := le_rfl
  have hUT : U ≤ Y.hom ⁻¹ᵁ ⊤ := le_top
  have hUY : (fst Y X).left ⁻¹ᵁ U =
      (snd Y X).left ⁻¹ᵁ ⊤ ⊓ (fst Y X).left ⁻¹ᵁ U := by simp
  have hq := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUT hUX hUY
    (isAffineOpen_top (Spec (.of k))) hU isCompact_univ isQuasiSeparated_univ
  have hp := (isIso_pushoutSection_iff H hUT hUX hUY).mp hq
  have : IsIso (X.hom.appLE ⊤ ⊤ hUX) := by
    change IsIso (X.hom.appLE ⊤ (X.hom ⁻¹ᵁ ⊤) le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact isIso_appTop_of_proper_integral X.hom
  have h := hp.isIso_inr_of_isIso
  change IsIso ((fst Y X).left.appLE U ((fst Y X).left ⁻¹ᵁ U) le_rfl) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

def properBaseChangeStructureSheafIso
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left] :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y.left ≅
      (Scheme.Modules.pushforward (fst Y X).left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Y ⊗ X).left) := by
  let q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y.left ⟶
      (Scheme.Modules.pushforward (fst Y X).left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Y ⊗ X).left) :=
    SheafOfModules.unitToPushforwardObjUnit (fst Y X).left.toRingCatSheafHom
  have : IsIso ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map q) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : Y.left.affineOpens ↦ U.1)
      (by simpa only [Subtype.range_val] using Y.left.isBasis_affineOpens)
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have := isIso_properBaseChange_app_of_isAffineOpen Y X U.1 U.2
    exact (ConcreteCategory.isIso_iff_bijective ((fst Y X).left.app U.1)).mp inferInstance
  have : IsIso ((Scheme.Modules.toPresheaf Y.left).map q) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map q)))
  have : IsIso q := isIso_of_reflects_iso q (Scheme.Modules.toPresheaf Y.left)
  exact asIso q

theorem isIso_properBaseChange_app
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left]
    (U : Y.left.Opens) : IsIso ((fst Y X).left.app U) := by
  let e := properBaseChangeStructureSheafIso Y X
  have h := (ConcreteCategory.isIso_iff_bijective (e.hom.app U)).mp inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
