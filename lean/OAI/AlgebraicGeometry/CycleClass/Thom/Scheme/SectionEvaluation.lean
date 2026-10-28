import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction

/-! # Section Evaluation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation

noncomputable section

/-! Actual section evaluation on arbitrary complex schemes and their opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev openOver (U : X.left.Opens) := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver X U
abbrev openInclusion (U : X.left.Opens) := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X U
abbrev analyticOpen (U : X.left.Opens) := ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X U
abbrev openPointHomeomorph (U : X.left.Opens) := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemePointHomeomorph X U

theorem openPointHomeomorph_val (U : X.left.Opens)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X U)) :
    (openPointHomeomorph X U p).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openInclusion X U) p := rfl

/-- Inclusion of one open complex subscheme into another. -/
abbrev openRestriction {V W : X.left.Opens} (h : V ≤ W) : openOver X V ⟶ openOver X W :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (W.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem openRestriction_inclusion {V W : X.left.Opens} (h : V ≤ W) :
    openRestriction X h ≫ openInclusion X W = openInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

theorem openPointHomeomorph_restrict {V W : X.left.Opens} (h : V ≤ W)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X V)) :
    openPointHomeomorph X W (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) p) =
      ⟨(openPointHomeomorph X V p).val, h (openPointHomeomorph X V p).property⟩ := by
  apply Subtype.ext
  simp only [openPointHomeomorph_val, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, openRestriction_inclusion]

/-- The section-ring identification on an open subscheme commutes with restriction. -/
theorem topIso_inv_restrict {V W : X.left.Opens} (h : V ≤ W) :
    X.left.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      W.topIso.inv ≫ (X.left.homOfLE h).appTop := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
  congr 1

/-- A regular section evaluated continuously on the corresponding analytic open. -/
def sectionEvaluationOn (W : X.left.Opens) (s : Γ(X.left, W)) :
    C(analyticOpen X W, ℂ) :=
  (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionContinuousMap (openOver X W) (W.topIso.inv s)).comp
    ⟨(openPointHomeomorph X W).symm, (openPointHomeomorph X W).symm.continuous⟩

theorem sectionEvaluationOn_mul (W : X.left.Opens)
    (s t : Γ(X.left, W)) (p : analyticOpen X W) :
    sectionEvaluationOn X W (s * t) p =
      sectionEvaluationOn X W s p * sectionEvaluationOn X W t p := by
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X W).symm p)
    (W.topIso.inv (s * t)) = _
  rw [map_mul, map_mul]
  rfl

theorem sectionEvaluationOn_unit_ne_zero (W : X.left.Opens)
    (u : Γ(X.left, W)ˣ) (p : analyticOpen X W) :
    sectionEvaluationOn X W (u : Γ(X.left, W)) p ≠ 0 := by
  exact DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_unit_ne_zero
    (X := openOver X W) (Units.map W.topIso.inv.hom.toMonoidHom u)
      ((openPointHomeomorph X W).symm p)

/-- Analytic evaluation commutes with the actual algebraic section restriction. -/
theorem sectionEvaluationOn_restrict {V W : X.left.Opens} (h : V ≤ W)
    (s : Γ(X.left, W)) (p : analyticOpen X V) :
    sectionEvaluationOn X V (X.left.presheaf.map (homOfLE h).op s) p =
      sectionEvaluationOn X W s ⟨p.val, h p.property⟩ := by
  have hp : (openPointHomeomorph X W).symm ⟨p.val, h p.property⟩ =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) ((openPointHomeomorph X V).symm p) := by
    apply (openPointHomeomorph X W).injective
    rw [Homeomorph.apply_symm_apply, openPointHomeomorph_restrict,
      Homeomorph.apply_symm_apply]
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X V).symm p)
      (V.topIso.inv (X.left.presheaf.map (homOfLE h).op s)) =
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X W).symm ⟨p.val, h p.property⟩)
      (W.topIso.inv s)
  rw [hp, DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X V).symm p))
    (ConcreteCategory.congr_hom (topIso_inv_restrict X h) s)

/-- Evaluation at a complex point is a homomorphism of the actual section ring. -/
def sectionEvaluationHom (U : X.left.Opens) (y : analyticOpen X U) : Γ(X.left, U) →+* ℂ :=
  (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X U).symm y)).comp U.topIso.inv.hom

theorem sectionEvaluationHom_apply (U : X.left.Opens) (y : analyticOpen X U)
    (s : Γ(X.left, U)) :
    sectionEvaluationHom X U y s = sectionEvaluationOn X U s y := rfl

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation
