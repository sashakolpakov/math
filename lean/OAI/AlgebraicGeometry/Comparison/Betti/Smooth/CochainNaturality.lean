import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainMap
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormNaturality
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback

/-! # Cochain Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainNaturality

noncomputable section

/-! Naturality of the constructed algebraic-to-smooth cochain map in all degrees. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u

variable {E F M N A B : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

attribute [local instance] SymbolPointwise.tangentNormedGroup SymbolPointwise.tangentNormedSpace

theorem manifoldWedge_pullback (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x) (a (g x)) (b (g x))).symm

variable
  (φA : A →ₐ[ℂ] C(M, ℂ)) (hA : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φA a))
  (φB : B →ₐ[ℂ] C(N, ℂ)) (hB : ∀ b, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ (φB b))
  (f : B →ₐ[ℂ] A) (g : M → N) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
  (hcomm : ∀ b x, φA (f b) x = φB b (g x))

include hcomm in
theorem smoothSymbol_naturality : ∀ (n : ℕ) (a : Fin (n + 1) → B),
    HigherSmoothSymbols.smoothSymbol φA hA n (f ∘ a) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (HigherSmoothSymbols.smoothSymbol φB hB n a) := by
  intro n
  induction n with
  | zero =>
      intro a
      exact FormNaturality.zeroFormMap_naturality φA hA φB hB f g hg hcomm (a 0)
  | succ n ih =>
      intro a
      rw [HigherSmoothSymbols.smoothSymbol_succ, HigherSmoothSymbols.smoothSymbol_succ, manifoldWedge_pullback]
      have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φA hA (f (a (Fin.last (n + 1))))) =
          Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg
            (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φB hB (a (Fin.last (n + 1))))) :=
        (congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
          (FormNaturality.zeroFormMap_naturality φA hA φB hB f g hg hcomm (a (Fin.last (n + 1))))).trans
          (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback g hg _)
      exact congrArg₂ AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (ih (Fin.init a)) hd

include hcomm in
theorem smoothFormMap_naturality (n : ℕ) (a : Algebraic.Forms.Form B n) :
    CochainMap.smoothFormMap φA hA n (Algebraic.Forms.pullback f n a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (CochainMap.smoothFormMap φB hB n a) := by
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations B n).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol B a := by
        simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul]
      apply congrArg (c • ·)
      change CochainMap.smoothFormMap φA hA n (Algebraic.Forms.pullback f n (Algebraic.Forms.formSymbol B a)) =
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg (CochainMap.smoothFormMap φB hB n (Algebraic.Forms.formSymbol B a))
      rw [Algebraic.Forms.pullback_symbol, CochainMap.smoothFormMap_symbol, CochainMap.smoothFormMap_symbol]
      exact smoothSymbol_naturality φA hA φB hB f g hg hcomm n a

include hcomm in
/-- Naturality is an equality of the constructed cochain morphisms. -/
theorem smoothCochainMap_naturality :
    Algebraic.Forms.complexPullback f ≫ CochainMap.smoothCochainMap φA hA =
      CochainMap.smoothCochainMap φB hB ≫ Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamPullback g hg := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact smoothFormMap_naturality φA hA φB hB f g hg hcomm n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CochainNaturality
