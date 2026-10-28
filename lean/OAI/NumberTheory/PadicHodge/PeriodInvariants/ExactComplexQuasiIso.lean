import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Exact Complex Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExactComplexQuasiIso.Short

/-! # Quasi-isomorphisms on the outer terms of short exact sequences induce one on the middle term -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.ComposableArrows
open _root_.HomologicalComplex _root_.HomologicalComplex.HomologySequence

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem middle {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  have := h₁
  have := h₃
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hprev : (ComplexShape.up ℤ).Rel (i - 1) i := by change i - 1 + 1 = i; omega
  have hnext : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
  have : Mono (homologyMap φ.τ₂ i) := by
    apply Abelian.mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i hprev))
    · exact (composableArrows₅_exact hS₁ (i - 1) i hprev).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ (i - 1) i hprev).δ₀.δ₀
    · exact inferInstanceAs (Epi (homologyMap φ.τ₃ (i - 1)))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₁ i))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₃ i))
  have : Epi (homologyMap φ.τ₂ i) := by
    apply Abelian.epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) hnext))
    · exact (composableArrows₅_exact hS₁ i (i + 1) hnext).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i (i + 1) hnext).δlast.δlast
    · exact inferInstanceAs (Epi (homologyMap φ.τ₁ i))
    · exact inferInstanceAs (Epi (homologyMap φ.τ₃ i))
    · exact inferInstanceAs (Mono (homologyMap φ.τ₁ (i + 1)))
  exact isIso_of_mono_of_epi _

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExactComplexQuasiIso.Short
