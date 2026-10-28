import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback

/-! # Restricted Section Square -/

namespace OAI.RepresentationTheory.Theta.Geometric.RestrictedSectionSquare

noncomputable section

/-! Actual restricted section pullbacks agree around a commuting square,
with the canonical sheaf pullback isomorphisms kept explicit. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction

universe u

theorem restrictedSection_pullbackCongr {X Y : Scheme.{u}}
    (f g : Y ⟶ X) (h : f = g) (M : X.Modules) (W : X.Opens) (V : Y.Opens)
    (hf : V ≤ f ⁻¹ᵁ W) (hg : V ≤ g ⁻¹ᵁ W) (a : Γ(M, W)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app V
      (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M W V hf a) =
      AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map g M W V hg a := by
  subst g
  rfl

theorem restrictedSection_square {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (W : X.Opens) (hs : (⊤ : S.Opens) ≤ s ⁻¹ᵁ W)
    (hb : (⊤ : T.Opens) ≤ b ⁻¹ᵁ (f ⁻¹ᵁ W)) (a : Γ(M, W)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
      (((Scheme.Modules.pullbackComp b f).hom.app M).app ⊤
        (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map b ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ W) ⊤ hb
          (AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M W a))) =
      ((Scheme.Modules.pullbackComp g s).hom.app M).app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback g ((Scheme.Modules.pullback s).obj M)
          (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map s M W ⊤ hs a)) := by
  have hf := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp f b M W (f ⁻¹ᵁ W) ⊤ le_rfl hb a
  rw [AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.full] at hf
  have hg := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp s g M W ⊤ ⊤ hs (by simp) a
  exact (congrArg (((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤) hf).trans
    ((restrictedSection_pullbackCongr (b ≫ f) (g ≫ s) h M W ⊤
      (fun _ ht => hb ht) (fun _ ht => hs ht) a).trans hg.symm)

theorem restrictedSection_square_open {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (W : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ W)
    (hs : (⊤ : S.Opens) ≤ s ⁻¹ᵁ W) (hb : (⊤ : T.Opens) ≤ b ⁻¹ᵁ V) (a : Γ(M, W)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
      (((Scheme.Modules.pullbackComp b f).hom.app M).app ⊤
        (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map b ((Scheme.Modules.pullback f).obj M) V ⊤ hb
          (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M W V hV a))) =
      ((Scheme.Modules.pullbackComp g s).hom.app M).app ⊤
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback g ((Scheme.Modules.pullback s).obj M)
          (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map s M W ⊤ hs a)) := by
  have hf := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp f b M W V ⊤ hV hb a
  have hg := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp s g M W ⊤ ⊤ hs (by simp) a
  exact (congrArg (((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤) hf).trans
    ((restrictedSection_pullbackCongr (b ≫ f) (g ≫ s) h M W ⊤
      (fun _ ht => hV (hb ht)) (fun _ ht => hs ht) a).trans hg.symm)

end

end OAI.RepresentationTheory.Theta.Geometric.RestrictedSectionSquare
