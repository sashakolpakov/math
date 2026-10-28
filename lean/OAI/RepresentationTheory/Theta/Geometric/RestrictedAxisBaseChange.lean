import OAI.RepresentationTheory.Theta.Geometric.RestrictedSectionSquare
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback

/-! # Restricted Axis Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.RestrictedAxisBaseChange

noncomputable section

/-! Pulling a local cochain coefficient around the actual parameter
square transports its rigidified axis value by the base ring map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem restrictedAxisValue_baseChange {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (W : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ W) (hs : (⊤ : S.Opens) ≤ s ⁻¹ᵁ W)
    (hb : (⊤ : T.Opens) ≤ b ⁻¹ᵁ V) (a : Γ(M, W)) :
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
      (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map b ((Scheme.Modules.pullback f).obj M) V ⊤ hb
        (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M W V hV a)) =
      g.appTop (r.hom.app ⊤ (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map s M W ⊤ hs a)) := by
  let z := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map b ((Scheme.Modules.pullback f).obj M) V ⊤ hb
    (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M W V hV a)
  let v := AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map s M W ⊤ hs a
  let w := AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback g ((Scheme.Modules.pullback s).obj M) v
  let E := (Scheme.Modules.pullbackComp g s).app M
  have hc : E.inv.app ⊤ (E.hom.app ⊤ w) = w :=
    congrArg (fun e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj M) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback s).obj M) => e.app ⊤ w) E.hom_inv_id
  have hsquare := RestrictedSectionSquare.restrictedSection_square_open f b g s h M W V hV hs hb a
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom.app ⊤
      (((Scheme.Modules.pullback g).map r.hom).app ⊤
        (E.inv.app ⊤ (((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤
          (((Scheme.Modules.pullbackComp b f).hom.app M).app ⊤ z)))) = _
  rw [hsquare]
  refine (congrArg (fun x => (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom.app ⊤
    (((Scheme.Modules.pullback g).map r.hom).app ⊤ x)) hc).trans ?_
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom.app ⊤
    (((Scheme.Modules.pullback g).map r.hom).app ⊤
      (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback g ((Scheme.Modules.pullback s).obj M) v)) = _
  rw [AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback.Construction.globalLineSectionPullback_eq]
  have hn := AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.naturality g r.hom ⊤ v
  exact (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom.app ⊤) hn.symm).trans
    (AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback.Construction.StructurePullbackValues.apply g ⊤ (r.hom.app ⊤ v))

end

end OAI.RepresentationTheory.Theta.Geometric.RestrictedAxisBaseChange
