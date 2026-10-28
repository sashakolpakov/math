import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionComposition

/-! # Restricted Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback

noncomputable section

/-! Composition of actual section pullbacks with specified source opens. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.RestrictedPullbackSections

variable {X Y Z : Scheme.{u}}

def map (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, V) :=
  ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)

theorem full (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    RestrictedPullbackSections.map f M U (f ⁻¹ᵁ U) le_rfl s = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem comp (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ g ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp g f).hom.app M).app W
      (RestrictedPullbackSections.map g ((Scheme.Modules.pullback f).obj M) V W hWV (RestrictedPullbackSections.map f M U V hVU s)) =
    RestrictedPullbackSections.map (g ≫ f) M U W (fun _ hz => hVU (hWV hz)) s := by
  let N := (Scheme.Modules.pullback f).obj M
  let P := (Scheme.Modules.pullback g).obj N
  let Q := (Scheme.Modules.pullback (g ≫ f)).obj M
  let e := (Scheme.Modules.pullbackComp g f).hom.app M
  let hW : W ≤ (g ≫ f) ⁻¹ᵁ U := fun _ hz => hVU (hWV hz)
  change e.app W (P.presheaf.map (homOfLE hWV).op
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map g N V
      (N.presheaf.map (homOfLE hVU).op (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)))) = _
  rw [PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict]
  rw [← P.presheaf.map_comp_apply]
  change e.app W (P.presheaf.map (homOfLE hW).op
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map g N (f ⁻¹ᵁ U) (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s))) = _
  have he := PresheafOfModules.naturality_apply e.val (homOfLE hW).op
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map g N (f ⁻¹ᵁ U) (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s))
  change e.app W (P.presheaf.map (homOfLE hW).op _) =
    Q.presheaf.map (homOfLE hW).op (e.app ((g ≫ f) ⁻¹ᵁ U) _) at he
  exact he.trans (congrArg (Q.presheaf.map (homOfLE hW).op)
    (PullbackSectionComposition.Construction.PullbackSectionCoefficients.comp f g M U s))

end Construction.RestrictedPullbackSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback
