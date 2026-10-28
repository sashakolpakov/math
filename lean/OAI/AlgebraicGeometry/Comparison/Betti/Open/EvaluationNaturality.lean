import OAI.AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.EvaluationNaturality

noncomputable section

/-!
# Evaluation on opens under an arbitrary complex scheme map

The maps on regular sections and complex points are those of the original
scheme morphism. The proof uses the actual restriction to open subschemes.
The open-subscheme calculation generalizes the one in
`SectionEvaluationNaturality` to arbitrary schemes over the complex base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)
  (U : Y.left.Opens) (W : X.left.Opens) (hWU : W ≤ f.left ⁻¹ᵁ U)

/-- Restrict the original scheme map to the chosen open subschemes. -/
def openMapOver : AffineIsoEvaluation.openOver X W ⟶ AffineIsoEvaluation.openOver Y U :=
  Over.homMk (f.left.resLE U W hWU) (by
    change f.left.resLE U W hWU ≫ (U.ι ≫ Y.hom) = W.ι ≫ X.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    exact congrArg (fun g => W.ι ≫ g) f.w)

theorem openMapOver_inclusion :
    openMapOver f U W hWU ≫ AffineIsoEvaluation.openInclusion Y U = AffineIsoEvaluation.openInclusion X W ≫ f := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι f.left hWU

/-- The original map on complex points, restricted to the analytic opens. -/
def analyticOpenMap : C(AffineIsoEvaluation.analyticOpen X W, AffineIsoEvaluation.analyticOpen Y U) :=
  ⟨fun p => ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val, hWU p.property⟩,
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).comp continuous_subtype_val).subtype_mk _⟩

theorem openPointHomeomorph_map (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AffineIsoEvaluation.openOver X W)) :
    AffineIsoEvaluation.openPointHomeomorph Y U (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openMapOver f U W hWU) p) =
      analyticOpenMap f U W hWU (AffineIsoEvaluation.openPointHomeomorph X W p) := by
  apply Subtype.ext
  simp only [AffineIsoEvaluation.openPointHomeomorph_val, analyticOpenMap, ContinuousMap.coe_mk,
    ← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, openMapOver_inclusion]

theorem topIso_inv_appLE :
    f.left.appLE U W hWU ≫ W.topIso.inv =
      U.topIso.inv ≫ (openMapOver f U W hWU).left.appTop := by
  change _ = U.topIso.inv ≫ (f.left.resLE U W hWU).app ⊤
  erw [Scheme.Hom.resLE_app_top, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- Evaluating a pulled-back regular section evaluates the section at the mapped point. -/
theorem sectionEvaluationOn_appLE (s : Γ(Y.left, U)) (p : AffineIsoEvaluation.analyticOpen X W) :
    AffineIsoEvaluation.sectionEvaluationOn X W (f.left.appLE U W hWU s) p =
      AffineIsoEvaluation.sectionEvaluationOn Y U s (analyticOpenMap f U W hWU p) := by
  have hp : (AffineIsoEvaluation.openPointHomeomorph Y U).symm (analyticOpenMap f U W hWU p) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (openMapOver f U W hWU) ((AffineIsoEvaluation.openPointHomeomorph X W).symm p) := by
    apply (AffineIsoEvaluation.openPointHomeomorph Y U).injective
    rw [Homeomorph.apply_symm_apply, openPointHomeomorph_map,
      Homeomorph.apply_symm_apply]
  change RegularFunctions.globalEvaluation ((AffineIsoEvaluation.openPointHomeomorph X W).symm p)
      (W.topIso.inv (f.left.appLE U W hWU s)) =
    RegularFunctions.globalEvaluation ((AffineIsoEvaluation.openPointHomeomorph Y U).symm (analyticOpenMap f U W hWU p))
      (U.topIso.inv s)
  rw [hp, RegularFunctions.globalEvaluation_map]
  exact congrArg (RegularFunctions.globalEvaluation ((AffineIsoEvaluation.openPointHomeomorph X W).symm p))
    (ConcreteCategory.congr_hom (topIso_inv_appLE f U W hWU) s)

/-- The scalar-compatible section map agrees with the same pointwise evaluation. -/
theorem sectionEvaluationOn_pullback (s : Γ(Y.left, U))
    (p : AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) :
    AffineIsoEvaluation.sectionEvaluationOn X (f.left ⁻¹ᵁ U) (Algebraic.Sheaves.sectionPullback f U s) p =
      AffineIsoEvaluation.sectionEvaluationOn Y U s (analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl p) := by
  change AffineIsoEvaluation.sectionEvaluationOn X (f.left ⁻¹ᵁ U) (f.left.app U s) p = _
  rw [f.left.app_eq_appLE]
  exact sectionEvaluationOn_appLE f U (f.left ⁻¹ᵁ U) le_rfl s p

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.EvaluationNaturality
