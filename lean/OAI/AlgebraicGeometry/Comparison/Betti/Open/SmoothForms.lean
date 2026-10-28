import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.GlobalSmoothCochain
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham

/-! # Smooth Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms

noncomputable section

/-!
# Restriction-compatible realization on every open

Algebraic forms on a Zariski open are realized as actual smooth forms on its
analytic inverse image. The construction handles empty opens and intertwines
both exterior differentiation and the genuine open restriction maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

omit [IsIntegral X.left] [Smooth X.hom] in
theorem analyticOpen_mono {V U : X.left.Opens} (h : V ≤ U) : AffineIsoEvaluation.analyticOpen X V ≤ AffineIsoEvaluation.analyticOpen X U :=
  fun _ hp => h hp

/-- Realize algebraic sections as smooth forms on the actual inverse-image open. -/
def openSmoothFormMap (U : X.left.Opens) (n : ℕ) :
    Algebraic.Forms.Form Γ(X.left, U) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) n :=
  ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) n).symm.toLinearMap).comp
    (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X U) (SmoothEvaluation.sectionEvaluationOn_smooth X U) n)

theorem openSmoothFormMap_d (U : X.left.Opens) (n : ℕ) (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    openSmoothFormMap X U (n + 1) (Algebraic.Forms.differential Γ(X.left, U) n a) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (openSmoothFormMap X U n a) := by
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) (n + 1)).symm
      (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X U) (SmoothEvaluation.sectionEvaluationOn_smooth X U)
        (n + 1) (Algebraic.Forms.differential Γ(X.left, U) n a)) = _
  rw [Betti.Smooth.CochainMap.smoothFormMap_d]
  exact (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_symm_d _).symm

/-- The canonical map on open-section cochain complexes. -/
def openSmoothCochainMap (U : X.left.Opens) : Algebraic.Forms.algebraicDeRhamComplex Γ(X.left, U) ⟶
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (openSmoothFormMap X U n)) (fun n => by
    rw [Algebraic.Forms.algebraicDeRhamComplex_d, Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (openSmoothFormMap_d X U n a).symm)

/-- Algebraic restriction and smooth open restriction commute in every degree. -/
theorem openSmoothFormMap_restrict {V U : X.left.Opens} (h : V ≤ U) (n : ℕ)
    (a : Algebraic.Forms.Form Γ(X.left, U) n) :
    openSmoothFormMap X V n (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) n a) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (analyticOpen_mono X h) (openSmoothFormMap X U n a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X V) n).injective
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X V) n
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X V) n).symm
        (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X V) (SmoothEvaluation.sectionEvaluationOn_smooth X V) n
          (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) n a))) = _
  rw [LinearEquiv.apply_symm_apply, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict]
  change Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X V) (SmoothEvaluation.sectionEvaluationOn_smooth X V) n
      (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) n a) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Opens.inclusion (analyticOpen_mono X h))
      (contMDiff_inclusion (I := 𝓘(ℝ, RegularSmoothness.NativeModel X)) (n := ∞) _)
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) n
        ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RegularSmoothness.NativeModel X) (AffineIsoEvaluation.analyticOpen X U) n).symm
          (Betti.Smooth.CochainMap.smoothFormMap (AffineIsoEvaluation.sectionEvaluationOn X U) (SmoothEvaluation.sectionEvaluationOn_smooth X U) n a)))
  rw [LinearEquiv.apply_symm_apply]
  exact Betti.Smooth.CochainNaturality.smoothFormMap_naturality
    (AffineIsoEvaluation.sectionEvaluationOn X V) (SmoothEvaluation.sectionEvaluationOn_smooth X V)
    (AffineIsoEvaluation.sectionEvaluationOn X U) (SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) (Opens.inclusion (analyticOpen_mono X h))
    (contMDiff_inclusion (I := 𝓘(ℝ, RegularSmoothness.NativeModel X)) (n := ∞) _)
    (fun s p => AffineIsoEvaluation.sectionEvaluationOn_restrict X h s p) n a

theorem openSmoothCochainMap_restrict {V U : X.left.Opens} (h : V ≤ U) :
    Algebraic.Forms.complexPullback (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op) ≫ openSmoothCochainMap X V =
      openSmoothCochainMap X U ≫ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict (RegularSmoothness.NativeModel X) (analyticOpen_mono X h) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact openSmoothFormMap_restrict X h n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms
