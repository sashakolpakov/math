import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing
import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothNaturality

/-! # Kaehler Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality

noncomputable section

/-! The constructed Kähler-to-smooth realization commutes with actual
affine scheme pullback, in particular finite étale correspondence maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothNaturality

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem affineForm_pullbackLE (U : Y.left.Opens) (W : X.left.Opens)
    (hWU : W ≤ f.left ⁻¹ᵁ U) (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    Kaehler.affineForm X W hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Comparison.Betti.Algebraic.Forms.pullback
        ((Comparison.Betti.Algebraic.Sheaves.sectionRestriction X (homOfLE hWU).op).comp (Comparison.Betti.Algebraic.Sheaves.sectionPullback f U)) 1
          (Kaehler.affineForm Y U hU form) := by
  let r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y U ⟶
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X W :=
    CommAlgCat.ofHom ((Comparison.Betti.Algebraic.Sheaves.sectionRestriction X (homOfLE hWU).op).comp (Comparison.Betti.Algebraic.Sheaves.sectionPullback f U))
  have hr : AbelianScheme.TateComparison.FormConstants.affineComplexMap r ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X W hW ≫ f := by
    apply Over.OverMorphism.ext
    change Spec.map (f.left.appLE U W hWU) ≫ hU.fromSpec = hW.fromSpec ≫ f.left
    exact IsAffineOpen.SpecMap_appLE_fromSpec f.left hU hW hWU
  have hn := form.property _ _ r (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU)
  rw [hr] at hn
  exact (congrArg (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm Γ(X.left, W)) hn.symm).trans
    (Kaehler.kaehlerToOneForm_naturality r _)

theorem affineForm_pullback (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hW : IsAffineOpen (f.left ⁻¹ᵁ U)) (form : AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    Kaehler.affineForm X (f.left ⁻¹ᵁ U) hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Comparison.Betti.Algebraic.Forms.pullback (Comparison.Betti.Algebraic.Sheaves.sectionPullback f U) 1 (Kaehler.affineForm Y U hU form) := by
  let r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra Y U ⟶
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X (f.left ⁻¹ᵁ U) :=
    CommAlgCat.ofHom (Comparison.Betti.Algebraic.Sheaves.sectionPullback f U)
  have hr : AbelianScheme.TateComparison.FormConstants.affineComplexMap r ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X (f.left ⁻¹ᵁ U) hW ≫ f := by
    apply Over.OverMorphism.ext
    change Spec.map (f.left.app U) ≫ hU.fromSpec = hW.fromSpec ≫ f.left
    rw [f.left.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f.left hU hW le_rfl
  have hn := form.property _ _ r (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y U hU)
  rw [hr] at hn
  exact (congrArg (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm Γ(X.left, f.left ⁻¹ᵁ U)) hn.symm).trans
    (Kaehler.kaehlerToOneForm_naturality r _)

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

theorem affineSmoothForm_pullbackLE (U : Y.left.Opens) (W : X.left.Opens)
    (hWU : W ≤ f.left ⁻¹ᵁ U) (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    Kaehler.affineSmoothForm X W hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (Comparison.Betti.Open.SmoothForms.analyticOpen_mono X hWU)
        ((Comparison.Betti.Open.SmoothNaturality.openSmoothPullback f U).f 1 (Kaehler.affineSmoothForm Y U hU form)) := by
  change Comparison.Betti.Open.SmoothForms.openSmoothFormMap X W 1 (Kaehler.affineForm X W hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form)) = _
  rw [affineForm_pullbackLE f U W hWU hU hW, Comparison.Betti.Algebraic.Forms.pullback_comp]
  change Comparison.Betti.Open.SmoothForms.openSmoothFormMap X W 1
    (Comparison.Betti.Algebraic.Forms.pullback (Comparison.Betti.Algebraic.Sheaves.sectionRestriction X (homOfLE hWU).op) 1
      (Comparison.Betti.Algebraic.Forms.pullback (Comparison.Betti.Algebraic.Sheaves.sectionPullback f U) 1 (Kaehler.affineForm Y U hU form))) = _
  rw [Comparison.Betti.Open.SmoothForms.openSmoothFormMap_restrict X hWU, Comparison.Betti.Open.SmoothNaturality.openSmoothFormMap_naturality f U]
  rfl

theorem affineSmoothForm_pullback (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hW : IsAffineOpen (f.left ⁻¹ᵁ U)) (form : AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    Kaehler.affineSmoothForm X (f.left ⁻¹ᵁ U) hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      (Comparison.Betti.Open.SmoothNaturality.openSmoothPullback f U).f 1 (Kaehler.affineSmoothForm Y U hU form) := by
  change Comparison.Betti.Open.SmoothForms.openSmoothFormMap X (f.left ⁻¹ᵁ U) 1
    (Kaehler.affineForm X (f.left ⁻¹ᵁ U) hW (AbelianScheme.TateComparison.FormConstants.formsPullback f form)) = _
  rw [affineForm_pullback f U hU hW]
  exact Comparison.Betti.Open.SmoothNaturality.openSmoothFormMap_naturality f U 1 _

theorem openSmoothPullback_onOpen (U : Y.left.Opens) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) n) :
    (Comparison.Betti.Open.SmoothNaturality.openSmoothPullback f U).f n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen Y U) form) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U))
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
          (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) form) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n).injective
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) n).symm
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Comparison.Betti.Open.EvaluationNaturality.analyticOpenMap f U (f.left ⁻¹ᵁ U) le_rfl)
          (Comparison.Betti.Open.SmoothNaturality.analyticOpenMap_smooth f U (f.left ⁻¹ᵁ U) le_rfl)
          (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel Y) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen Y U) n
            (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen Y U) form)))) = _
  rw [LinearEquiv.apply_symm_apply, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen,
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen, ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp,
    ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  rfl

variable [X.left.IsSeparated] [Y.left.IsSeparated]

/-- Affine neighborhoods in the source refine inverse images, so no affineness
condition is needed on the actual algebraic map. -/
theorem globalSmoothForm_pullback (form : AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    KaehlerGluing.globalSmoothForm X (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) (KaehlerGluing.globalSmoothForm Y form) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro p
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (KaehlerGluing.affineAnalytic_cover Y (Set.mem_univ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)))
  have hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ f.left ⁻¹ᵁ i.val := hi
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWU⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hpU (f.left ⁻¹ᵁ i.val).isOpen
  have h := affineSmoothForm_pullbackLE f i.val W hWU i.property hW form
  rw [← KaehlerGluing.globalSmoothForm_onAffine X _ _ hW,
    ← KaehlerGluing.globalSmoothForm_onAffine Y _ _ i.property, openSmoothPullback_onOpen] at h
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X)
    (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X W) 1 => a ⟨p, hpW⟩) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality
