import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RigidityRestrictionOn

/-! # Relative Functions Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions

noncomputable section

/-! Global functions descend along a proper smooth morphism with connected
geometric fibers and a section, when its source is reduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f]
variable [GeometricallyConnected f] [IsReduced X]
variable (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

include he

theorem section_appTop_comp : e.appTop ≫ f.appTop = 𝟙 Γ(X, ⊤) := by
  have h := congrArg Scheme.Hom.appTop
    (RelativeAffine.Construction.RelativeAffineRigidity.factor f e he X.toSpecΓ)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
  simpa only [Category.comp_id, Category.assoc] using h.symm

/-- Restriction to the section is inverse to pullback on global functions. -/
def iso : Γ(S, ⊤) ≅ Γ(X, ⊤) where
  hom := f.appTop
  inv := e.appTop
  hom_inv_id := by rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  inv_hom_id := section_appTop_comp f e he

theorem isIso_appTop : IsIso f.appTop := (iso f e he).isIso_hom

theorem section_appTop_injective : Function.Injective e.appTop := by
  have : IsIso e.appTop := (iso f e he).isIso_inv
  exact (ConcreteCategory.isIso_iff_bijective e.appTop).mp this |>.injective

/-- The same descent holds over every open of the base. -/
theorem isIso_restrict_appTop (V : S.Opens) : IsIso (f ∣_ V).appTop :=
  isIso_appTop (f ∣_ V) (RigidityRestrictionOn.Construction.RigidityRestriction.section_restrict f e he V)
    (RigidityRestrictionOn.Construction.RigidityRestriction.section_restrict_comp_base f e he V)

theorem isIso_app (V : S.Opens) : IsIso (f.app V) := by
  let t := X.presheaf.map (eqToHom (image_morphismRestrict_preimage f V ⊤)).op
  have ht : IsIso t :=
    X.presheaf.map_isIso _
  have h : IsIso (f.app (V.ι ''ᵁ ⊤) ≫ t) := by
    rw [← morphismRestrict_appTop]
    exact isIso_restrict_appTop f e he V
  have h' : IsIso (f.app (V.ι ''ᵁ ⊤)) :=
    (isIso_comp_right_iff (f.app (V.ι ''ᵁ ⊤)) t).mp h
  exact (congrArg (fun W : S.Opens => IsIso (f.app W)) V.ι_image_top).mp h'

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs.Construction.RelativeFunctions
