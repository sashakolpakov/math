import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicCartan
import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionPurity
import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionAnticommutation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime

/-! # Antiholomorphic Contraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.AntiholomorphicContraction.Dolbeault

noncomputable section

/-! Constant antiholomorphic contraction on actual smooth open-domain forms.
Its local Cartan identity uses the original open Dolbeault differential. -/

open _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {U V : Opens E}

def openAntiContraction (U : Opens E) (n : ℕ) (v : E) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n where
  toFun a := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U (fun x => AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension x))
    (((AntiholomorphicContraction.Dolbeault.antiContraction n v).restrictScalars ℝ).contDiff.comp_contDiffOn a.smooth)
  map_add' a b := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change AntiholomorphicContraction.Dolbeault.antiContraction n v ((a + b).extension x) =
      AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension x) + AntiholomorphicContraction.Dolbeault.antiContraction n v (b.extension x)
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_add]
    exact map_add _ _ _
  map_smul' c a := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change AntiholomorphicContraction.Dolbeault.antiContraction n v ((c • a).extension x) = c • AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension x)
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_smul]
    exact (AntiholomorphicContraction.Dolbeault.antiContraction n v).map_smul c (a.extension x)

omit [IsScalarTower ℝ ℂ E] in
@[simp] theorem openAntiContraction_apply (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (x : U) :
    openAntiContraction U n v a x = AntiholomorphicContraction.Dolbeault.antiContraction n v (a x) := by
  change AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension x) = _
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply]

omit [IsScalarTower ℝ ℂ E] in
theorem openAntiContraction_restrict (h : V ≤ U) (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h (openAntiContraction U n v a) =
      openAntiContraction V n v (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h a) := by
  ext x w
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply, openAntiContraction_apply]

theorem openAntiContraction_pure (p q : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q + 1)) (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) :
    DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q (openAntiContraction U (p + q) v a) := by
  intro x z w
  simp only [openAntiContraction_apply]
  exact AntiholomorphicContractionPurity.Dolbeault.antiContraction_pure p q v (a x) (ha x) z w

omit [IsScalarTower ℝ ℂ E] in
theorem openAntiContraction_squared (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 2)) :
    openAntiContraction U n v (openAntiContraction U (n + 1) v a) = 0 := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  simp only [openAntiContraction_apply, AntiholomorphicContractionAnticommutation.Dolbeault.antiContraction_squared, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply]

theorem openDolbeaultD_antiContraction (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (x : U) :
    DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n (openAntiContraction U n v a) x +
      openAntiContraction U (n + 1) v (DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a) x =
        Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (fderiv ℝ a.extension x) v := by
  have heq : (openAntiContraction U n v a).extension =ᶠ[𝓝 (x : E)]
      (fun y => AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension y)) :=
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_ofRaw_eventuallyEq _ _ x
  rw [DivisorClass.Chern.DolbeaultOpen.openDolbeaultD_apply, openAntiContraction_apply, DivisorClass.Chern.DolbeaultOpen.openDolbeaultD_apply]
  have hd : Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (openAntiContraction U n v a).extension x =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => AntiholomorphicContraction.Dolbeault.antiContraction n v (a.extension y)) x := by
    unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
    rw [heq.fderiv_eq]
  rw [hd]
  exact AntiholomorphicCartan.Dolbeault.extDerivDoublePrime_antiContraction n v a.extension
    ((a.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.AntiholomorphicContraction.Dolbeault
