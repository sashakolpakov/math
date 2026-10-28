import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.SchemeBaseChange

/-! # Constant Trivialization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-! Actual global trivializations of the finite etale torsor when its cohomology class vanishes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- An actual global torsor lift trivializes its actual scheme as the finite constant cover. -/
def App.Construction.FiniteCoefficientExtension.gluedConstantIso (s : E.Fiber (Scheme.ProEt.mk (𝟙 X))) :
    Over.mk E.gluedSchemeToBase ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X (ULift.{u} (ZMod (ℓ ^ n))) := by
  let U := Scheme.ProEt.mk (𝟙 X)
  let e₀ : E.gluedProEt ≅ E.gluedProEt ⨯ U := {
    hom := prod.lift (𝟙 _) ((GlobalSections.Construction.proEtaleIdentityIsTerminal X).from E.gluedProEt)
    inv := prod.fst
    hom_inv_id := by simp
    inv_hom_id := by
      apply prod.hom_ext
      · simp
      · exact (GlobalSections.Construction.proEtaleIdentityIsTerminal X).hom_ext _ _ }
  let e := e₀ ≪≫ (Over.forget U).mapIso (E.gluedTrivialization U s)
  let e' := (Scheme.ProEt.forget X ⋙ Over.forget X).mapIso e
  refine Over.isoMk e' ?_
  change e.hom.left ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X (ULift.{u} (ZMod (ℓ ^ n)))).hom = E.gluedSchemeToBase
  have he : e.hom.left ≫ ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X (ULift.{u} (ZMod (ℓ ^ n)))).hom ≫ 𝟙 X) =
      E.gluedSchemeToBase := MorphismProperty.Over.w e.hom
  simpa only [Category.comp_id] using he

/-- Vanishing of the actual cohomology class supplies this actual constant-cover isomorphism. -/
def App.Construction.FiniteCoefficientExtension.gluedConstantIsoOfClassEqZero (h : E.extClass = 0) :
    Over.mk E.gluedSchemeToBase ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X (ULift.{u} (ZMod (ℓ ^ n))) := by
  let s := (E.class_eq_zero_iff_scheme_section.mp h).choose
  have hs : s ≫ E.gluedSchemeToBase = 𝟙 X := (E.class_eq_zero_iff_scheme_section.mp h).choose_spec
  let a : Scheme.ProEt.mk (𝟙 X) ⟶ E.gluedProEt := MorphismProperty.Over.homMk s hs
  exact E.gluedConstantIso (E.gluedRepresentative.homEquiv a)

/-- Vanishing after the actual cohomological pullback trivializes the original scheme's
literal geometric base change. -/
def App.Construction.FiniteCoefficientExtension.baseChangeConstantIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (h : Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 E.extClass = 0) :
    Over.mk (pullback.snd E.gluedSchemeToBase f) ≅
      AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y (ULift.{u} (ZMod (ℓ ^ n))) :=
  (Scheme.ProEt.forget Y).mapIso (E.baseChangeGluedIso f) ≪≫
    (E.pullbackExtension f).gluedConstantIsoOfClassEqZero
      ((E.pullbackExtension_extClass f).trans h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
