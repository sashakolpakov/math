import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticTransitions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # Analytic Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-!
# ChernClass: evaluation on the actual analytic open cover

Open subschemes are identified with their actual open subsets of complex
points. Regular sections and the constructed frame-transition units are
evaluated through these homeomorphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Inclusion of the actual open complex subscheme. -/
abbrev Line.Bundles.AlgebraicLineBundle.openInclusion (W : X.carrier.Opens) : Line.Bundles.AlgebraicLineBundle.openOver W ⟶ X.toOver :=
  Over.homMk W.ι rfl

instance Line.Bundles.AlgebraicLineBundle.openInclusion_isOpenImmersion (W : X.carrier.Opens) :
    IsOpenImmersion (Line.Bundles.AlgebraicLineBundle.openInclusion X W).left := by
  change IsOpenImmersion W.ι
  infer_instance

/-- Inclusion of one open complex subscheme into another. -/
abbrev Line.Bundles.AlgebraicLineBundle.openRestriction {V W : X.carrier.Opens} (h : V ≤ W) : Line.Bundles.AlgebraicLineBundle.openOver V ⟶ Line.Bundles.AlgebraicLineBundle.openOver W :=
  Over.homMk (X.carrier.homOfLE h) (by
    change X.carrier.homOfLE h ≫ (W.ι ≫ X.structureMap) = V.ι ≫ X.structureMap
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem Line.Bundles.AlgebraicLineBundle.openRestriction_inclusion {V W : X.carrier.Opens} (h : V ≤ W) :
    Line.Bundles.AlgebraicLineBundle.openRestriction X h ≫ Line.Bundles.AlgebraicLineBundle.openInclusion X W = Line.Bundles.AlgebraicLineBundle.openInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.carrier h

/-- An algebraic open subset gives its actual analytic open subset. -/
def Line.Bundles.AlgebraicLineBundle.analyticOpen (W : X.carrier.Opens) : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (W : Set X.carrier), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpen_preimage_underlying _ W.isOpen⟩

/-- The established open-immersion homeomorphism, with the image written as an open set. -/
def Line.Bundles.AlgebraicLineBundle.openPointHomeomorph (W : X.carrier.Opens) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W) ≃ₜ Line.Bundles.AlgebraicLineBundle.analyticOpen X W :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (Line.Bundles.AlgebraicLineBundle.openInclusion X W)).trans
    (Homeomorph.setCongr (by
      change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X.toOver)) ⁻¹' Set.range W.ι =
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X.toOver)) ⁻¹' (W : Set X.carrier)
      rw [Scheme.Opens.range_ι]))

@[simp]
theorem Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_val (W : X.carrier.Opens)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)) :
    (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W p).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Line.Bundles.AlgebraicLineBundle.openInclusion X W) p := rfl

theorem Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_restrict {V W : X.carrier.Opens} (h : V ≤ W)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver V)) :
    Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Line.Bundles.AlgebraicLineBundle.openRestriction X h) p) =
      ⟨(Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X V p).val, h (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X V p).property⟩ := by
  apply Subtype.ext
  simp only [Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_val, ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, Line.Bundles.AlgebraicLineBundle.openRestriction_inclusion]

/-- The section-ring identification on an open subscheme commutes with restriction. -/
theorem Line.Bundles.AlgebraicLineBundle.topIso_inv_restrict {V W : X.carrier.Opens} (h : V ≤ W) :
    X.carrier.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      W.topIso.inv ≫ (X.carrier.homOfLE h).appTop := by
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop, ← Functor.map_comp]
  congr 1

/-- A regular section evaluated continuously on the corresponding analytic open. -/
def Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn (W : X.carrier.Opens) (s : Γ(X.carrier, W)) :
    C(Line.Bundles.AlgebraicLineBundle.analyticOpen X W, ℂ) :=
  (AnalyticTransitions.Construction.globalSectionContinuousMap (Line.Bundles.AlgebraicLineBundle.openOver W) (W.topIso.inv s)).comp
    ⟨(Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm, (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm.continuous⟩

theorem Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul (W : X.carrier.Opens)
    (s t : Γ(X.carrier, W)) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (s * t) p =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W s p * Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W t p := by
  change AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm p)
    (W.topIso.inv (s * t)) = _
  rw [map_mul, map_mul]
  rfl

theorem Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero (W : X.carrier.Opens)
    (u : Γ(X.carrier, W)ˣ) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (u : Γ(X.carrier, W)) p ≠ 0 := by
  exact AnalyticTransitions.Construction.globalSectionEvaluation_unit_ne_zero
    (X := Line.Bundles.AlgebraicLineBundle.openOver W) (Units.map W.topIso.inv.hom.toMonoidHom u)
      ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm p)

/-- Analytic evaluation commutes with the actual algebraic section restriction. -/
theorem Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict {V W : X.carrier.Opens} (h : V ≤ W)
    (s : Γ(X.carrier, W)) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X V) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X V (X.carrier.presheaf.map (homOfLE h).op s) p =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W s ⟨p.val, h p.property⟩ := by
  have hp : (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm ⟨p.val, h p.property⟩ =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Line.Bundles.AlgebraicLineBundle.openRestriction X h) ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X V).symm p) := by
    apply (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).injective
    rw [Homeomorph.apply_symm_apply, Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_restrict,
      Homeomorph.apply_symm_apply]
  change AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X V).symm p)
      (V.topIso.inv (X.carrier.presheaf.map (homOfLE h).op s)) =
    AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X W).symm ⟨p.val, h p.property⟩)
      (W.topIso.inv s)
  rw [hp, AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X V).symm p))
    (ConcreteCategory.congr_hom (Line.Bundles.AlgebraicLineBundle.topIso_inv_restrict X h) s)

end

/-!
# ChernClass: actual section evaluation under a complex scheme map

Evaluation on algebraic opens commutes with the original map of schemes,
via its genuine maps on sections and complex points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : Y.toOver ⟶ X.toOver)
  (U : X.carrier.Opens) (W : Y.carrier.Opens) (hWU : W ≤ f.left ⁻¹ᵁ U)

/-- Restrict the actual complex scheme map to the specified algebraic opens. -/
def Line.Bundles.AlgebraicLineBundle.openMapOver : Line.Bundles.AlgebraicLineBundle.openOver W ⟶ Line.Bundles.AlgebraicLineBundle.openOver U :=
  Over.homMk (f.left.resLE U W hWU) (by
    change f.left.resLE U W hWU ≫ (U.ι ≫ X.structureMap) = W.ι ≫ Y.structureMap
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    exact congrArg (fun g => W.ι ≫ g) f.w)

theorem Line.Bundles.AlgebraicLineBundle.openMapOver_inclusion :
    Line.Bundles.AlgebraicLineBundle.openMapOver f U W hWU ≫ Line.Bundles.AlgebraicLineBundle.openInclusion X U = Line.Bundles.AlgebraicLineBundle.openInclusion Y W ≫ f := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι f.left hWU

/-- The map on actual analytic open subsets. -/
def Line.Bundles.AlgebraicLineBundle.analyticOpenMap : C(Line.Bundles.AlgebraicLineBundle.analyticOpen Y W, Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
  ⟨fun p => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val, hWU p.property⟩,
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).comp continuous_subtype_val).subtype_mk _⟩

theorem Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_map (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Line.Bundles.AlgebraicLineBundle.openOver W)) :
    Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Line.Bundles.AlgebraicLineBundle.openMapOver f U W hWU) p) =
      Line.Bundles.AlgebraicLineBundle.analyticOpenMap f U W hWU (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph Y W p) := by
  apply Subtype.ext
  simp only [Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_val, Line.Bundles.AlgebraicLineBundle.analyticOpenMap, ContinuousMap.coe_mk,
    ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, Line.Bundles.AlgebraicLineBundle.openMapOver_inclusion]

/-- The actual top-section map agrees with the original map on the chosen opens. -/
theorem Line.Bundles.AlgebraicLineBundle.topIso_inv_appLE :
    f.left.appLE U W hWU ≫ W.topIso.inv =
      U.topIso.inv ≫ (Line.Bundles.AlgebraicLineBundle.openMapOver f U W hWU).left.appTop := by
  change _ = U.topIso.inv ≫ (f.left.resLE U W hWU).app ⊤
  rw [Scheme.Hom.resLE_app_top, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Evaluation of a pulled-back regular section is evaluation at the mapped point. -/
theorem Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appLE (s : Γ(X.carrier, U)) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen Y W) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (f.left.appLE U W hWU s) p =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U s (Line.Bundles.AlgebraicLineBundle.analyticOpenMap f U W hWU p) := by
  have hp : (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U).symm (Line.Bundles.AlgebraicLineBundle.analyticOpenMap f U W hWU p) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Line.Bundles.AlgebraicLineBundle.openMapOver f U W hWU) ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph Y W).symm p) := by
    apply (Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U).injective
    rw [Homeomorph.apply_symm_apply, Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_map,
      Homeomorph.apply_symm_apply]
  change AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph Y W).symm p)
      (W.topIso.inv (f.left.appLE U W hWU s)) =
    AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph X U).symm (Line.Bundles.AlgebraicLineBundle.analyticOpenMap f U W hWU p))
      (U.topIso.inv s)
  rw [hp, AnalyticTransitions.Construction.globalSectionEvaluation_map]
  exact congrArg (AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph Y W).symm p))
    (ConcreteCategory.congr_hom (Line.Bundles.AlgebraicLineBundle.topIso_inv_appLE f U W hWU) s)

/-- For an open immersion this is the actual scalar isomorphism on its image. -/
theorem Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appIso [IsOpenImmersion f.left]
    (s : Γ(X.carrier, f.left ''ᵁ W)) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen Y W) :
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W ((f.left.appIso W).hom s) p =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (f.left ''ᵁ W) s
        (Line.Bundles.AlgebraicLineBundle.analyticOpenMap f (f.left ''ᵁ W) W (f.left.preimage_image_eq W).ge p) := by
  rw [Scheme.Hom.appIso_hom']
  exact Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appLE f (f.left ''ᵁ W) W (f.left.preimage_image_eq W).ge s p

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
