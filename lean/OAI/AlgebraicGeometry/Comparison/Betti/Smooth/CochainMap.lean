import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Cochain Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap

noncomputable section

/-!
# Actual algebraic-to-smooth de Rham cochain map

The map is induced by evaluation and differentiation of functions, followed
by actual exterior multiplication. Every algebraic presentation relation
and every cochain square is proved before descending to the form quotient.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u

variable {E M A : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

/-- The actual smooth realization of algebraic forms in every degree. -/
def smoothFormMap (n : ℕ) : Algebraic.Forms.Form A n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  (Algebraic.Forms.relations A n).liftQ (HigherSmoothSymbols.rawSmoothMap φ hφ n)
    (Submodule.span_le.mpr (fun _ hr => SymbolPointwise.rawSmoothMap_relation_zero φ hφ hr))

@[simp]
theorem smoothFormMap_symbol (n : ℕ) (a : Fin (n + 1) → A) :
    smoothFormMap φ hφ n (Algebraic.Forms.formSymbol A a) = HigherSmoothSymbols.smoothSymbol φ hφ n a :=
  HigherSmoothSymbols.rawSmoothMap_symbol φ hφ n a

theorem smoothFormMap_d (n : ℕ) (a : Algebraic.Forms.Form A n) :
    smoothFormMap φ hφ (n + 1) (Algebraic.Forms.differential A n a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (smoothFormMap φ hφ n a) := by
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A n).mkQ_surjective a
  exact HigherSmoothSymbols.rawSmoothMap_d φ hφ n r

/-- The all-degree construction extends the already checked degree-zero realization. -/
theorem smoothFormMap_zero :
    smoothFormMap φ hφ 0 = (FormRealization.zeroFormMap φ hφ).comp (Algebraic.Forms.zeroEvaluation A) := by
  apply LinearMap.ext
  intro a
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A 0).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol A a := by
        simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul]
      apply congrArg (c • ·)
      change HigherSmoothSymbols.rawSmoothMap φ hφ 0 (Algebraic.Forms.symbol A a) =
        FormRealization.zeroFormMap φ hφ (Algebraic.Forms.rawZeroEvaluation A (Algebraic.Forms.symbol A a))
      rw [HigherSmoothSymbols.rawSmoothMap_symbol, Algebraic.Forms.rawZeroEvaluation_symbol]
      rfl

/-- The higher-degree construction agrees with the universal Kähler-based one-form map. -/
theorem smoothFormMap_one : smoothFormMap φ hφ 1 = FormRealization.oneFormMap φ hφ := by
  let := FormRealization.formSectionModule φ hφ 1
  let := FormRealization.formSectionScalarTower φ hφ 1
  let := FormRealization.formSectionSmulComm φ hφ 1
  change smoothFormMap φ hφ 1 = OneFormRealization.oneFormRealization (FormRealization.functionDerivation φ hφ)
  apply OneFormRealization.oneFormRealization_unique
  intro a
  rw [smoothFormMap_symbol]
  change AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (FormRealization.zeroFormMap φ hφ (a 0))
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φ hφ (a 1))) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ (a 0)) (hφ (a 0))
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φ hφ (a 1)))
  exact Wedge.manifoldWedge_zeroForm_one φ hφ _ _

/-- The canonical map of actual cochain complexes, with no comparison assumption. -/
def smoothCochainMap : Algebraic.Forms.algebraicDeRhamComplex A ⟶ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (smoothFormMap φ hφ n)) (fun n => by
    rw [Algebraic.Forms.algebraicDeRhamComplex_d, Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (smoothFormMap_d φ hφ n a).symm)

/-- Normalization of the cochain map on every regular differential-form generator. -/
theorem smoothCochainMap_symbol (n : ℕ) (a : Fin (n + 1) → A) :
    (smoothCochainMap φ hφ).f n (Algebraic.Forms.formSymbol A a) = HigherSmoothSymbols.smoothSymbol φ hφ n a :=
  smoothFormMap_symbol φ hφ n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap
