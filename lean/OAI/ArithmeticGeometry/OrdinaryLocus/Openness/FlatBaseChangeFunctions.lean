import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardPullback
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Flat Base Change Functions -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeFunctions.Construction

noncomputable section

/-! A quasi-compact quasi-separated map preserving functions continues to do so after flat base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (p : Z ⟶ X) (q : Z ⟶ Y)
variable (H : IsPullback p q f g) [QuasiCompact f] [QuasiSeparated f] [Flat g]
variable (hf : ∀ U : S.Opens, IsIso (f.app U))

include H hf

theorem isIso_app_flat_baseChange_of_affine
    (U : Y.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ g ⁻¹ᵁ V) :
    IsIso (q.app U) := by
  have hZ : q ⁻¹ᵁ U = p ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ q ⁻¹ᵁ U := by
    simp_rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hUV]
  have hT := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUV le_rfl hZ hV hU
    (f.isCompact_preimage hV.isCompact) (f.isQuasiSeparated_preimage hV.isQuasiSeparated)
  have hP := (isIso_pushoutSection_iff H hUV le_rfl hZ).mp hT
  have : IsIso (f.appLE V (f ⁻¹ᵁ V) le_rfl) := by rw [Scheme.Hom.appLE_eq_app]; exact hf V
  have hi := hP.isIso_inr_of_isIso
  change IsIso (q.appLE U (q ⁻¹ᵁ U) le_rfl) at hi
  rw [Scheme.Hom.appLE_eq_app] at hi
  exact hi

def flatBaseChangeStructureSheafIso :
    LineBundle.Construction.structureSheafModule Y ≅ (Scheme.Modules.pushforward q).obj (LineBundle.Construction.structureSheafModule Z) := by
  let B : Set Y.Opens := {U | IsAffineOpen U ∧ ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ g ⁻¹ᵁ V}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W y hy
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show g y ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUW⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ W ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩)
    exact ⟨U, ⟨hU, V, hV, hUW.trans inf_le_right⟩, hyU, hUW.trans inf_le_left⟩
  let e : LineBundle.Construction.structureSheafModule Y ⟶ (Scheme.Modules.pushforward q).obj (LineBundle.Construction.structureSheafModule Z) :=
    SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom
  have : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map e) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : B ↦ U.1)
      (by simpa only [Subtype.range_val] using hB)
    intro U
    obtain ⟨V, hV, hUV⟩ := U.2.2
    have := isIso_app_flat_baseChange_of_affine f g p q H hf U.1 V U.2.1 hV hUV
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso (q.app U.1))
  have : IsIso ((Scheme.Modules.toPresheaf Y).map e) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map e)))
  have : IsIso e := isIso_of_reflects_iso e (Scheme.Modules.toPresheaf Y)
  exact asIso e

theorem isIso_app_flat_baseChange (U : Y.Opens) : IsIso (q.app U) := by
  let e := flatBaseChangeStructureSheafIso f g p q H hf
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso (e.hom.app U))

theorem picardPullback_flat_baseChange_injective : Function.Injective (PicardPullback.Construction.picardPullback q) :=
  PicardPullback.Construction.picardPullback_injective_of_app q (isIso_app_flat_baseChange f g p q H hf)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeFunctions.Construction
