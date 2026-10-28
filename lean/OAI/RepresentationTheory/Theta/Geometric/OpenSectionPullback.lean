import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

/-! # Open Section Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenSectionPullback

noncomputable section

/-! Exact top-section coordinates of pullback along a restricted morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem open_appLE_self {X : Scheme} (U : X.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

theorem morphismRestrict_topSection {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
  let V := f ⁻¹ᵁ U
  have hleft := Scheme.Hom.appLE_comp_appLE (f ∣_ U) U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (fun _ _ => trivial)
  have hright := Scheme.Hom.appLE_comp_appLE V.ι f U V ⊤ le_rfl V.ι_preimage_self.ge
  have ht : (f ∣_ U).appLE ⊤ ⊤ (fun _ _ => trivial) = (f ∣_ U).appTop :=
    (f ∣_ U).appLE_eq_app
  rw [open_appLE_self, ht] at hleft
  rw [open_appLE_self, Scheme.Hom.appLE_eq_app] at hright
  apply hleft.trans
  apply Eq.trans _ hright.symm
  congr 1
  exact morphismRestrict_ι f U

theorem morphismRestrict_topSection_apply {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv r) = (f ⁻¹ᵁ U).topIso.inv (f.app U r) :=
  ConcreteCategory.congr_hom (morphismRestrict_topSection f U) r

end

end OAI.RepresentationTheory.Theta.Geometric.OpenSectionPullback
