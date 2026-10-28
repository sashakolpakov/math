import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Kaehler
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Kaehler Gluing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing

noncomputable section

/-! Global smooth realization of TateComparison's actual affine-test Kähler forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [X.left.IsSeparated]

abbrev AffineOpenIndex := {U : X.left.Opens // IsAffineOpen U}

omit [IsIntegral X.left] [Smooth X.hom] [X.left.IsSeparated] in
theorem affineAnalytic_cover : (Set.univ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆
    ⋃ i : AffineOpenIndex X, (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
  intro p _
  let j := X.left.affineCover.idx (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  let U := (X.left.affineCover.f j).opensRange
  refine Set.mem_iUnion.mpr ⟨⟨U, isAffineOpen_opensRange (X.left.affineCover.f j)⟩, ?_⟩
  exact X.left.affineCover.covers (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)

theorem affineSmoothForm_compatible (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible
      (fun i : AffineOpenIndex X => Kaehler.affineSmoothForm X i.val i.property form) := by
  intro i j p hi hj
  let hW : IsAffineOpen (i.val ⊓ j.val) := i.property.inf j.property
  have hleft := Kaehler.affineSmoothForm_restrict X inf_le_left i.property hW form
  have hright := Kaehler.affineSmoothForm_restrict X inf_le_right j.property hW form
  have h := hleft.symm.trans hright
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X)
    (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (i.val ⊓ j.val)) 1 => a ⟨p, ⟨hi, hj⟩⟩) h

def globalSmoothFormValue (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue
    (fun _ : AffineOpenIndex X => le_top) (affineAnalytic_cover X)
    (fun i : AffineOpenIndex X => Kaehler.affineSmoothForm X i.val i.property form)
    (affineSmoothForm_compatible X form))

theorem globalSmoothFormValue_apply (form : AbelianScheme.TateComparison.FormConstants.OneForms X) (i : AffineOpenIndex X)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hp : p ∈ Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val) :
    globalSmoothFormValue X form p = Kaehler.affineSmoothForm X i.val i.property form ⟨p, hp⟩ := by
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply _ p).trans
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue_apply _ (affineAnalytic_cover X) _
      (affineSmoothForm_compatible X form)
      (⟨p, Set.mem_univ p⟩ : (⊤ : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) i hp)

/-- Actual global smooth one-forms, glued from their canonical affine restrictions. -/
def globalSmoothForm :
    AbelianScheme.TateComparison.FormConstants.OneForms X →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 1 where
  toFun := globalSmoothFormValue X
  map_add' form other := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro p
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (affineAnalytic_cover X (Set.mem_univ p))
    rw [globalSmoothFormValue_apply X (form + other) i p hi]
    change _ = globalSmoothFormValue X form p + globalSmoothFormValue X other p
    rw [globalSmoothFormValue_apply X form i p hi,
      globalSmoothFormValue_apply X other i p hi]
    exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X)
      (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val) 1 => a ⟨p, hi⟩) (map_add (Kaehler.affineSmoothForm X i.val i.property) form other)
  map_smul' c form := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro p
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (affineAnalytic_cover X (Set.mem_univ p))
    rw [globalSmoothFormValue_apply X (c • form) i p hi]
    change _ = c • globalSmoothFormValue X form p
    rw [globalSmoothFormValue_apply X form i p hi]
    exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (Comparison.Betti.RegularSmoothness.NativeModel X)
      (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val) 1 => a ⟨p, hi⟩) (map_smul (Kaehler.affineSmoothForm X i.val i.property) c form)

theorem globalSmoothForm_onAffine (form : AbelianScheme.TateComparison.FormConstants.OneForms X) (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) (globalSmoothForm X form) =
      Kaehler.affineSmoothForm X U hU form := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  exact globalSmoothFormValue_apply X form ⟨U, hU⟩ p p.property

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing
