import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.KaehlerEquivalence
import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms

/-! # Kaehler -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Kaehler

noncomputable section

/-!
# Realizing TateComparison's actual Kähler forms on affine opens

Evaluate the affine-test form on the canonical spectrum of each affine
open's section ring. The proved Kähler presentation equivalence then feeds
the genuine algebraic-to-smooth de Rham map. Compatibility follows from
the form's affine-test naturality and the actual scheme restriction maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

theorem kaehlerToOneForm_naturality {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (form : KaehlerDifferential ℂ R) :
    Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm S (AbelianScheme.TateComparison.FormConstants.differentialMap f form) =
      Comparison.Betti.Algebraic.Forms.pullback f.hom 1 (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm R form) := by
  obtain ⟨r, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ R form
  induction r using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add r t hr ht => simp only [map_add, hr, ht]
  | single b a =>
    simp only [Finsupp.linearCombination_single, RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_smul,
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_D, Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm_smul_D,
      Comparison.Betti.KaehlerEquivalence.oneSymbol, Comparison.Betti.Algebraic.Forms.pullback_symbol]
    congr 1
    funext i
    fin_cases i <;> rfl

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual algebraic representative on a genuine affine Zariski open. -/
def affineForm (U : X.left.Opens) (hU : IsAffineOpen U) :
    AbelianScheme.TateComparison.FormConstants.OneForms X →ₗ[ℂ] Comparison.Betti.Algebraic.Forms.Form Γ(X.left, U) 1 where
  toFun form := Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm Γ(X.left, U)
    (form.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU))
  map_add' form η := map_add _ _ _
  map_smul' c form := by
    exact (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm Γ(X.left, U)).map_smul c
      (form.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU))

theorem affineForm_restrict {V U : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    affineForm X V hV form = Comparison.Betti.Algebraic.Forms.pullback
      (Comparison.Betti.Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) 1 (affineForm X U hU form) := by
  let f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U ⟶
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V :=
    CommAlgCat.ofHom (Comparison.Betti.Algebraic.Sheaves.sectionRestriction X (homOfLE h).op)
  have hf : AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X V hV := by
    apply Over.OverMorphism.ext
    exact hU.map_fromSpec hV (homOfLE h).op
  have hn := form.property _ _ f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)
  rw [hf] at hn
  exact (congrArg (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm Γ(X.left, V)) hn.symm).trans
    (kaehlerToOneForm_naturality f _)

variable [IsIntegral X.left] [Smooth X.hom]

/-- Genuine smooth forms on the analytic inverse image of each affine open. -/
def affineSmoothForm (U : X.left.Opens) (hU : IsAffineOpen U) :
    AbelianScheme.TateComparison.FormConstants.OneForms X →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1 :=
  (Comparison.Betti.Open.SmoothForms.openSmoothFormMap X U 1).comp (affineForm X U hU)

theorem affineSmoothForm_restrict {V U : X.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    affineSmoothForm X V hV form = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
      (Comparison.Betti.Open.SmoothForms.analyticOpen_mono X h) (affineSmoothForm X U hU form) := by
  change Comparison.Betti.Open.SmoothForms.openSmoothFormMap X V 1 (affineForm X V hV form) = _
  rw [affineForm_restrict X h hU hV]
  exact Comparison.Betti.Open.SmoothForms.openSmoothFormMap_restrict X h 1 _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Kaehler
