import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorOpenComparison
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Module Local Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleLocalIso.Construction

noncomputable section

/-! Detecting isomorphisms of module sheaves on open neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem isIso_restrictMap_of_pullbackMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (q : M ⟶ N)
    [IsIso ((Scheme.Modules.pullback f).map q)] :
    IsIso ((Scheme.Modules.restrictFunctor f).map q) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have : IsIso ((Scheme.Modules.restrictFunctor f).map q ≫ e.hom.app N) := by
    rw [e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app N)

theorem isIso_app_of_isIso_pullback {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N) (U V : X.Opens) (hVU : V ≤ U)
    [IsIso ((Scheme.Modules.pullback U.ι).map q)] : IsIso (q.app V) := by
  have := isIso_restrictMap_of_pullbackMap U.ι q
  have h := Scheme.Modules.Hom.isIso_iff_isIso_app.mp this (U.ι ⁻¹ᵁ V)
  change IsIso (q.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) at h
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  exact heq ▸ h

theorem isIso_of_locally_isIso_pullback {X : Scheme.{u}} {M N : X.Modules}
    (q : M ⟶ N)
    (hq : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map q)) :
    IsIso q := by
  let B : Set X.Opens := {V | ∃ U : X.Opens, V ≤ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map q)}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hxW
    obtain ⟨U, hxU, hU⟩ := hq x
    exact ⟨U ⊓ W, ⟨U, inf_le_left, hU⟩, ⟨hxU, hxW⟩, inf_le_right⟩
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map q) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : B ↦ U.1)
      (by simpa only [Subtype.range_val] using hB)
    intro V
    obtain ⟨U, hVU, hU⟩ := V.2
    have := @isIso_app_of_isIso_pullback X M N q U V.1 hVU hU
    exact this
  have : IsIso ((Scheme.Modules.toPresheaf X).map q) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map q)))
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf X)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleLocalIso.Construction
