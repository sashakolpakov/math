import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.BaseCoverInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.EffectiveDescent

/-! # Fpqc Parameter Classification -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcParameterClassification.Construction

noncomputable section

/-! A natural parameter classification that is bijective over a
faithfully flat base cover descends when sections of its target presheaf
are detected on that cover. The parameter morphisms descend effectively. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.EffectiveDescent

variable {S Y : Scheme.{0}} (p : Y ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    {E : Over S} {F : (Over S)ᵒᵖ ⥤ Type 1} (i : uliftYoneda.{1}.obj E ⟶ F)
    (hi : ∀ T : Over Y, Function.Bijective (i.app (.op ((Over.map p).obj T))))

include hi in
omit [QuasiCompact p] in
set_option backward.isDefEq.respectTransparency false in
theorem fpqc_parameterMap_injective (T : Over S) : Function.Injective (i.app (.op T)) := by
  intro a b h
  let u := (Over.mapPullbackAdj p).counit.app T
  have : Epi u.left := Flat.epi_of_flat_of_surjective (pullback.fst T.hom p)
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply (cancel_epi u.left).mp
  have he := (hi ((Over.pullback p).obj T)).injective
    ((i.naturality_apply u.op a).trans ((congrArg (F.map u.op) h).trans
      (i.naturality_apply u.op b).symm))
  exact congrArg (fun z => z.down.left) he

include hi in
set_option backward.isDefEq.respectTransparency false in
theorem fpqc_parameterMap_bijective
    (hF : ∀ T : Over S, Function.Injective ((Picard.BaseCoverInjection.Construction.baseCoverRestrictionMap p F).app (.op T)))
    (T : Over S) : Function.Bijective (i.app (.op T)) := by
  refine ⟨fpqc_parameterMap_injective p i hi T, ?_⟩
  intro x
  let U := (Over.pullback p).obj T
  let u := (Over.mapPullbackAdj p).counit.app T
  have : Flat u.left := inferInstanceAs (Flat (pullback.fst T.hom p))
  have : Surjective u.left := inferInstanceAs (Surjective (pullback.fst T.hom p))
  have : QuasiCompact u.left := inferInstanceAs (QuasiCompact (pullback.fst T.hom p))
  obtain ⟨a, ha⟩ := (hi U).surjective (F.map u.op x)
  have hc {V : Over S} (b c : V ⟶ (Over.map p).obj U) (hbc : b ≫ u = c ≫ u) :
      b ≫ a.down = c ≫ a.down := by
    have he : (ULift.up (b ≫ a.down) : ULift.{1} (V ⟶ E)) = ULift.up (c ≫ a.down) := by
      apply fpqc_parameterMap_injective p i hi V
      have hb := i.naturality_apply b.op a
      have hd := i.naturality_apply c.op a
      rw [ha] at hb hd
      have hmap : F.map b.op (F.map u.op x) = F.map c.op (F.map u.op x) :=
        (ConcreteCategory.congr_hom (F.map_comp u.op b.op) x).symm.trans
          ((congrArg (fun v : V ⟶ T => F.map v.op x) hbc).trans
            (ConcreteCategory.congr_hom (F.map_comp u.op c.op) x))
      exact hb.trans (hmap.trans hd.symm)
    exact congrArg ULift.down he
  obtain ⟨d, hd, _⟩ := AbelianModuli.HilbertConstruction.Over.EffectiveDescent.over_existsUnique_factor_of_effectiveEpi u a.down hc
  refine ⟨ULift.up d, ?_⟩
  apply hF T
  have hn := i.naturality_apply u.op (show (uliftYoneda.{1}.obj E).obj (.op T) from ULift.up d)
  have he : (uliftYoneda.{1}.obj E).map u.op (ULift.up d) = a := by
    apply ULift.ext
    exact hd
  exact hn.symm.trans ((congrArg (i.app (.op ((Over.map p).obj U))) he).trans ha)

include hi in
theorem fpqc_parameterMap_isIso
    (hF : ∀ T : Over S, Function.Injective ((Picard.BaseCoverInjection.Construction.baseCoverRestrictionMap p F).app (.op T))) :
    IsIso i := by
  have (T : (Over S)ᵒᵖ) : IsIso (i.app T) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (fpqc_parameterMap_bijective p i hi hF T.unop)
  exact NatIso.isIso_of_isIso_app i

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcParameterClassification.Construction
