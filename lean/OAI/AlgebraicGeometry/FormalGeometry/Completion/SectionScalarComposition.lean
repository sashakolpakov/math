import OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction

/-! # Section Scalar Composition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionScalarComposition

noncomputable section

/-! Successive geometric section pullbacks transport coefficients by the
actual map on base functions and respect the pullback-composition isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

def basePullbackCompSections {X Y Z T : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (τ : Z ⟶ T) (M : X.Modules) (W : Z.Opens) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj M))).obj (op W) →ₗ[Γ(T, ⊤)]
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback (j ≫ f)).obj M)).obj (op W) :=
  (((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor τ).map ((Scheme.Modules.pullbackComp j f).hom.app M)).app (op W)).hom

theorem basePullbackCompSections_apply {X Y Z T : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (τ : Z ⟶ T) (M : X.Modules) (W : Z.Opens)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj M))).obj (op W)) :
    basePullbackCompSections f j τ M W s = ((Scheme.Modules.pullbackComp j f).hom.app M).app W s := rfl

theorem restrictedSection_smul_comp {X Y Z T T' : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (ρ : Y ⟶ T) (τ : Z ⟶ T') (t : T' ⟶ T) (h : j ≫ ρ = τ ≫ t) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hj : W ≤ j ⁻¹ᵁ V)
    (r : Γ(T, ⊤)) (s : Γ(M, U)) :
    basePullbackCompSections f j τ M W
      (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map j ((Scheme.Modules.pullback f).obj M) V W hj
        (@SMul.smul Γ(T, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op V))
          inferInstance r (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hf s))) =
      @SMul.smul Γ(T', ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback (j ≫ f)).obj M)).obj (op W))
        inferInstance (t.appTop r)
          (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map (j ≫ f) M U W (fun _ hw => hf (hj hw)) s) := by
  erw [BaseSectionPullbackRestriction.Construction.restrictedBaseSectionPullback_smul j ρ τ t h]
  exact ((basePullbackCompSections f j τ M W).map_smul (t.appTop r) _).trans
    (congrArg
      (fun z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback (j ≫ f)).obj M)).obj (op W) =>
        @SMul.smul Γ(T', ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf τ ((Scheme.Modules.pullback (j ≫ f)).obj M)).obj (op W))
          inferInstance (t.appTop r) z)
      (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp f j M U V W hf hj s))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionScalarComposition
