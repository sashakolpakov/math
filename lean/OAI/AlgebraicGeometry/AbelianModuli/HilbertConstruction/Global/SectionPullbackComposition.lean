import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EqualityAndPullbackValues

/-! # Section Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition

noncomputable section

/-! Canonical composition and equality comparisons for module pullback
preserve the actual global section morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y Z : Scheme.{u}}

theorem pullbackSection_composition (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Z.Modules} (s : Line.Bundles.structureModule Z ⟶ M) :
    Ample.LineBundles.pullbackSection a (Ample.LineBundles.pullbackSection b s) ≫ (Scheme.Modules.pullbackComp a b).hom.app M =
      Ample.LineBundles.pullbackSection (a ≫ b) s := by
  apply Section.EqualityAndPullbackValues.moduleSection_eq_of_cover _ (fun _ : Unit => (a ≫ b) ⁻¹ᵁ (⊤ : Z.Opens))
    (fun _ => ⟨(), trivial⟩)
  intro _
  let U : Z.Opens := ⊤
  let W : X.Opens := (a ≫ b) ⁻¹ᵁ U
  let e := (Scheme.Modules.pullbackComp a b).hom.app M
  let v := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
    ((Scheme.Modules.pullback b).obj M)).app (b ⁻¹ᵁ U)
  have ha := Section.EqualityAndPullbackValues.pullbackSection_value_on_preimage a (Ample.LineBundles.pullbackSection b s) (b ⁻¹ᵁ U)
  have hb := Section.EqualityAndPullbackValues.pullbackSection_value_on_preimage b s U
  change e.app W ((Ample.LineBundles.pullbackSection a (Ample.LineBundles.pullbackSection b s)).app W (1 : Γ(X, W))) =
    (Ample.LineBundles.pullbackSection (a ≫ b) s).app W (1 : Γ(X, W))
  exact (congrArg (e.app W) ha).trans
    ((congrArg (fun t => e.app W (v t)) hb).trans
      ((Pullback.UnitCompositionValues.pullbackUnit_comp_value a b M U (s.app U (1 : Γ(Z, U)))).trans
        (Section.EqualityAndPullbackValues.pullbackSection_value_on_preimage (a ≫ b) s U).symm))

theorem pullbackSection_equality {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f s ≫ (Scheme.Modules.pullbackCongr h).hom.app M = Ample.LineBundles.pullbackSection g s := by
  subst g
  exact Category.comp_id _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition
