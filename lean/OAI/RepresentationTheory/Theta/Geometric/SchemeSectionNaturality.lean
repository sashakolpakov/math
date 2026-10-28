import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Scheme Section Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality

noncomputable section

section

/-! Regular sections on arbitrary complex schemes evaluate continuously
on their actual analytic opens, compatibly with restriction. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace SchemeSectionEvaluation

open OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev openOver (W : X.left.Opens) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (W.ι ≫ X.hom)

/-- Inclusion of the actual open complex subscheme. -/
abbrev openInclusion (W : X.left.Opens) : openOver X W ⟶ X :=
  Over.homMk W.ι rfl

instance openInclusion_isOpenImmersion (W : X.left.Opens) :
    IsOpenImmersion (openInclusion X W).left := by
  change IsOpenImmersion W.ι
  infer_instance

/-- Inclusion of one open complex subscheme into another. -/
abbrev openRestriction {V W : X.left.Opens} (h : V ≤ W) : openOver X V ⟶ openOver X W :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (W.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem openRestriction_inclusion {V W : X.left.Opens} (h : V ≤ W) :
    openRestriction X h ≫ openInclusion X W = openInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

/-- An algebraic open subset gives its actual analytic open subset. -/
def analyticOpen (W : X.left.Opens) : Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set X.left), AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpen_preimage_underlying _ W.isOpen⟩

/-- The established open-immersion homeomorphism, with the image written as an open set. -/
def openPointHomeomorph (W : X.left.Opens) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X W) ≃ₜ analyticOpen X W :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (openInclusion X W)).trans
    (Homeomorph.setCongr (by
      change (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) ⁻¹' Set.range W.ι =
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) ⁻¹' (W : Set X.left)
      rw [Scheme.Opens.range_ι]))

@[simp]
theorem openPointHomeomorph_val (W : X.left.Opens)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X W)) :
    (openPointHomeomorph X W p).val = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openInclusion X W) p := rfl

theorem openPointHomeomorph_restrict {V W : X.left.Opens} (h : V ≤ W)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver X V)) :
    openPointHomeomorph X W (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) p) =
      ⟨(openPointHomeomorph X V p).val, h (openPointHomeomorph X V p).property⟩ := by
  apply Subtype.ext
  simp only [openPointHomeomorph_val, ← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, openRestriction_inclusion]

/-- The section-ring identification on an open subscheme commutes with restriction. -/
theorem topIso_inv_restrict {V W : X.left.Opens} (h : V ≤ W) :
    X.left.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      W.topIso.inv ≫ (X.left.homOfLE h).appTop := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
  congr 1

/-- A regular section evaluated continuously on the corresponding analytic open. -/
def sectionEvaluationOn (W : X.left.Opens) (s : Γ(X.left, W)) :
    C(analyticOpen X W, ℂ) :=
  (AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionContinuousMap (openOver X W) (W.topIso.inv s)).comp
    ⟨(openPointHomeomorph X W).symm, (openPointHomeomorph X W).symm.continuous⟩

theorem sectionEvaluationOn_mul (W : X.left.Opens)
    (s t : Γ(X.left, W)) (p : analyticOpen X W) :
    sectionEvaluationOn X W (s * t) p =
      sectionEvaluationOn X W s p * sectionEvaluationOn X W t p := by
  change AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X W).symm p)
    (W.topIso.inv (s * t)) = _
  rw [map_mul, map_mul]
  rfl

theorem sectionEvaluationOn_unit_ne_zero (W : X.left.Opens)
    (u : Γ(X.left, W)ˣ) (p : analyticOpen X W) :
    sectionEvaluationOn X W (u : Γ(X.left, W)) p ≠ 0 := by
  exact AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_unit_ne_zero
    (X := openOver X W) (Units.map W.topIso.inv.hom.toMonoidHom u)
      ((openPointHomeomorph X W).symm p)

/-- Analytic evaluation commutes with the actual algebraic section restriction. -/
theorem sectionEvaluationOn_restrict {V W : X.left.Opens} (h : V ≤ W)
    (s : Γ(X.left, W)) (p : analyticOpen X V) :
    sectionEvaluationOn X V (X.left.presheaf.map (homOfLE h).op s) p =
      sectionEvaluationOn X W s ⟨p.val, h p.property⟩ := by
  have hp : (openPointHomeomorph X W).symm ⟨p.val, h p.property⟩ =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openRestriction X h) ((openPointHomeomorph X V).symm p) := by
    apply (openPointHomeomorph X W).injective
    rw [Homeomorph.apply_symm_apply, openPointHomeomorph_restrict,
      Homeomorph.apply_symm_apply]
  change AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X V).symm p)
      (V.topIso.inv (X.left.presheaf.map (homOfLE h).op s)) =
    AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X W).symm ⟨p.val, h p.property⟩)
      (W.topIso.inv s)
  rw [hp, AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X V).symm p))
    (ConcreteCategory.congr_hom (topIso_inv_restrict X h) s)

end SchemeSectionEvaluation

end

/-!
# Actual section evaluation under arbitrary complex scheme maps

Evaluation on algebraic opens commutes with the original map of schemes,
via its genuine maps on sections and complex points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace SchemeSectionEvaluation

open OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : Y ⟶ X)
  (U : X.left.Opens) (W : Y.left.Opens) (hWU : W ≤ f.left ⁻¹ᵁ U)

/-- Restrict the actual complex scheme map to the specified algebraic opens. -/
def openMapOver : openOver Y W ⟶ openOver X U :=
  Over.homMk (f.left.resLE U W hWU) (by
    change f.left.resLE U W hWU ≫ (U.ι ≫ X.hom) = W.ι ≫ Y.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    exact congrArg (fun g => W.ι ≫ g) f.w)

theorem openMapOver_inclusion :
    openMapOver f U W hWU ≫ openInclusion X U = openInclusion Y W ≫ f := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι f.left hWU

/-- The map on actual analytic open subsets. -/
def analyticOpenMap : C(analyticOpen Y W, analyticOpen X U) :=
  ⟨fun p => ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val, hWU p.property⟩,
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).comp continuous_subtype_val).subtype_mk _⟩

theorem openPointHomeomorph_map (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (openOver Y W)) :
    openPointHomeomorph X U (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openMapOver f U W hWU) p) =
      analyticOpenMap f U W hWU (openPointHomeomorph Y W p) := by
  apply Subtype.ext
  simp only [openPointHomeomorph_val, analyticOpenMap, ContinuousMap.coe_mk,
    ← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, openMapOver_inclusion]

/-- The actual top-section map agrees with the original map on the chosen opens. -/
theorem topIso_inv_appLE :
    f.left.appLE U W hWU ≫ W.topIso.inv =
      U.topIso.inv ≫ (openMapOver f U W hWU).left.appTop := by
  change _ = U.topIso.inv ≫ (f.left.resLE U W hWU).app ⊤
  rw [Scheme.Hom.resLE_app_top, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Evaluation of a pulled-back regular section is evaluation at the mapped point. -/
theorem sectionEvaluationOn_appLE (s : Γ(X.left, U)) (p : analyticOpen Y W) :
    sectionEvaluationOn Y W (f.left.appLE U W hWU s) p =
      sectionEvaluationOn X U s (analyticOpenMap f U W hWU p) := by
  have hp : (openPointHomeomorph X U).symm (analyticOpenMap f U W hWU p) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openMapOver f U W hWU) ((openPointHomeomorph Y W).symm p) := by
    apply (openPointHomeomorph X U).injective
    rw [Homeomorph.apply_symm_apply, openPointHomeomorph_map,
      Homeomorph.apply_symm_apply]
  change AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph Y W).symm p)
      (W.topIso.inv (f.left.appLE U W hWU s)) =
    AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph X U).symm (analyticOpenMap f U W hWU p))
      (U.topIso.inv s)
  rw [hp, AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((openPointHomeomorph Y W).symm p))
    (ConcreteCategory.congr_hom (topIso_inv_appLE f U W hWU) s)

/-- For an open immersion this is the actual scalar isomorphism on its image. -/
theorem sectionEvaluationOn_appIso [IsOpenImmersion f.left]
    (s : Γ(X.left, f.left ''ᵁ W)) (p : analyticOpen Y W) :
    sectionEvaluationOn Y W ((f.left.appIso W).hom s) p =
      sectionEvaluationOn X (f.left ''ᵁ W) s
        (analyticOpenMap f (f.left ''ᵁ W) W (f.left.preimage_image_eq W).ge p) := by
  rw [Scheme.Hom.appIso_hom']
  exact sectionEvaluationOn_appLE f (f.left ''ᵁ W) W (f.left.preimage_image_eq W).ge s p

end SchemeSectionEvaluation

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality
