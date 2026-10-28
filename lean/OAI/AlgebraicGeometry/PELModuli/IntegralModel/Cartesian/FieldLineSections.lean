import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionPushforward
import OAI.AlgebraicGeometry.Picard.PoincareBundle.IsoDescent

/-! # Field Line Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FieldLineSections

noncomputable section

/-! Field-extension invariance on any actual cartesian square, with the
base maps retained in the linear structures on global sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u

def baseSectionsIsoPullbackEquiv {X Y S : Scheme.{u}} (e : Y ≅ X)
    (π : X ⟶ S) (M : X.Modules) :
    (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj M ≃ₗ[Γ(S, ⊤)]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (e.hom ≫ π)).obj ((Scheme.Modules.pullback e.hom).obj M) := by
  let : (Scheme.Modules.pullback e.hom).IsEquivalence := Picard.PoincareBundle.IsoDescent.pullback_isEquivalence e
  let a := Scheme.Modules.pullbackPushforwardAdjunction e.hom
  exact ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).mapIso (asIso (a.unit.app M))).toLinearEquiv.trans
    (Projective.SectionPushforward.PolarizationEmbedding.baseSectionsPushforwardEquiv e.hom π ((Scheme.Modules.pullback e.hom).obj M))

theorem fieldLineSections_cartesian_finrank
    {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsSeparated π] [QuasiCompact π]
    (L : X.Modules) (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L)
    (c : Y ⟶ X) (q : Y ⟶ Spec (.of K)) (φ : k →+* K)
    (h : IsPullback c q π (Spec.map (CommRingCat.ofHom φ))) :
    Module.finrank Γ(Spec (.of K), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor q).obj ((Scheme.Modules.pullback c).obj L)) =
        Module.finrank Γ(Spec (.of k), ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj L) := by
  let : Algebra k K := φ.toAlgebra
  let e := h.isoPullback
  let p := pullback.fst π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K)
  let r := pullback.snd π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K)
  have hc : e.hom ≫ p = c := h.isoPullback_hom_fst
  have hq : e.hom ≫ r = q := h.isoPullback_hom_snd
  let z : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback p).obj L) ≅
      (Scheme.Modules.pullback c).obj L :=
    (Scheme.Modules.pullbackComp e.hom p).app L ≪≫ (Scheme.Modules.pullbackCongr hc).app L
  have hs := (baseSectionsIsoPullbackEquiv e r ((Scheme.Modules.pullback p).obj L)).finrank_eq
  have hz := ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (e.hom ≫ r)).mapIso z).toLinearEquiv.finrank_eq
  have hq' := (((eqToIso (congrArg (fun a => SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor a) hq)).app
    ((Scheme.Modules.pullback c).obj L)).toLinearEquiv).finrank_eq
  exact (hq'.symm.trans (hz.symm.trans hs.symm)).trans
    (FieldLineSections.PolarizationEmbedding.fieldLineSections_baseChange_finrank π L hL)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FieldLineSections
