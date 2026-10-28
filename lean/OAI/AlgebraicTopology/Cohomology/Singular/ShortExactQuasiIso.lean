import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Short Exact Quasi Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso

/-!
# Quasi-isomorphisms on the first term of a short exact sequence

For a morphism between short exact sequences of actual complexes, a
quasi-isomorphism on the middle and last terms implies one on the first
term. The proof uses the five lemma on the genuine long exact homology
sequence and handles initial degrees using its initial injection.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.ComposableArrows _root_.HomologicalComplex _root_.HomologicalComplex.HomologySequence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}
variable {S₁ S₂ : ShortComplex (HomologicalComplex C c)}

/-- In a morphism of short exact sequences of complexes, quasi-isomorphisms
on the middle and last terms induce a quasi-isomorphism on the first term.
This applies in particular to nonnegative module-valued cochain complexes. -/
theorem quasiIso_first_of_shortExact (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
      (composableArrows₅_exact hS₁ i j hij).δ₀
      (composableArrows₅_exact hS₂ i j hij).δ₀
      (δ₀Functor.map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · change Epi (homologyMap φ.τ₂ i)
      infer_instance
    · change IsIso (homologyMap φ.τ₃ i)
      infer_instance
    · change IsIso (homologyMap φ.τ₂ j)
      infer_instance
    · change Mono (homologyMap φ.τ₃ j)
      infer_instance
  · have := hS₁.mono_f
    have := hS₂.mono_f
    have h₁ : Mono (homologyMap S₁.f j) :=
      mono_homologyMap_of_mono_of_not_rel S₁.f j (by simpa using hj)
    have h₂' : Mono (homologyMap S₂.f j) :=
      mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    apply Abelian.isIso_of_isIso_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) (composableArrows₂_exact hS₂ j)
      h₁ h₂'
    · change IsIso (homologyMap φ.τ₂ j)
      infer_instance
    · change Mono (homologyMap φ.τ₃ j)
      infer_instance

end OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso
