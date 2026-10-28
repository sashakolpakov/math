import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormRealization
import OAI.AlgebraicGeometry.Comparison.Betti.RegularSmoothness

/-! # Form Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality

noncomputable section

/-! Pullback compatibility in the genuine smooth de Rham form spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

section

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {A B : Type u} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  (φA : A →ₐ[ℂ] C(M, ℂ)) (hA : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φA a))
  (φB : B →ₐ[ℂ] C(N, ℂ)) (hB : ∀ b, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ (φB b))
  (f : B →ₐ[ℂ] A) (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
  (hcomm : ∀ b x, φA (f b) x = φB b (g x))

include hcomm in
theorem zeroFormMap_naturality (b : B) :
    FormRealization.zeroFormMap φA hA (f b) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (FormRealization.zeroFormMap φB hB b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  exact hcomm b x

include hcomm in
theorem oneFormMap_symbol_naturality (a : Fin 2 → B) :
    FormRealization.oneFormMap φA hA (Algebraic.Forms.pullback f 1 (Algebraic.Forms.formSymbol B a)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (FormRealization.oneFormMap φB hB (Algebraic.Forms.formSymbol B a)) := by
  rw [Algebraic.Forms.pullback_symbol, FormRealization.oneFormMap_symbol, FormRealization.oneFormMap_symbol]
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φA (f (a 0))) (hA (f (a 0)))
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φA hA (f (a 1)))) = _
  rw [zeroFormMap_naturality φA hA φB hB f g hg hcomm, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback]
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change φA (f (a 0)) x *
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φB hB (a 1)) (g x))
        (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (v i)) =
    φB (a 0) (g x) *
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φB hB (a 1)) (g x))
        (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x (v i))
  rw [hcomm]

include hcomm in
/-- Actual smooth-form pullback commutes with realization for all algebraic one-forms. -/
theorem oneFormMap_naturality (a : Algebraic.Forms.Form B 1) :
    FormRealization.oneFormMap φA hA (Algebraic.Forms.pullback f 1 a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (FormRealization.oneFormMap φB hB a) := by
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations B 1).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol B a := by
        simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul]
      exact congrArg (c • ·) (oneFormMap_symbol_naturality φA hA φB hB f g hg hcomm a)

end

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

/-- Regular functions as actual smooth manifold zero-forms. -/
def globalSmoothZeroForm : Γ(X.left, ⊤) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 0 :=
  FormRealization.zeroFormMap (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)

/-- Algebraic one-forms as actual smooth manifold one-forms. -/
def globalSmoothOneForm : Algebraic.Forms.Form Γ(X.left, ⊤) 1 →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 1 :=
  FormRealization.oneFormMap (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)

theorem globalSmoothOneForm_d0 (a : Algebraic.Forms.Form Γ(X.left, ⊤) 0) :
    globalSmoothOneForm X (Algebraic.Forms.differential Γ(X.left, ⊤) 0 a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (globalSmoothZeroForm X (Algebraic.Forms.zeroEvaluation Γ(X.left, ⊤) a)) :=
  FormRealization.oneFormMap_d0 (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞) a

variable {X} {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]

theorem globalSmoothOneForm_naturality (f : X ⟶ Y) (a : Algebraic.Forms.Form Γ(Y.left, ⊤) 1) :
    globalSmoothOneForm X (Algebraic.Forms.pullback (Algebraic.Sheaves.sectionPullback f ⊤) 1 a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞) (globalSmoothOneForm Y a) :=
  oneFormMap_naturality (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞) (RegularFunctions.globalSectionContinuousAlgHom Y)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff Y s ∞) (Algebraic.Sheaves.sectionPullback f ⊤)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)
    (fun _ _ => rfl) a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
