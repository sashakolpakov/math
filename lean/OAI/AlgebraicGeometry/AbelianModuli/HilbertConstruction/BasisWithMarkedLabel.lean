import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Basis With Marked Label -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisWithMarkedLabel

noncomputable section

/-! A basis chosen from a spanning labeled family can be required to
include a specified nonzero label, even when some labeled vectors coincide. -/
open scoped Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type v}

theorem spanningFamily_basis_containing_label (v : ι → V) (H : Set ι)
    (hspan : Submodule.span K (v '' H) = ⊤) (i₀ : ι) (hi₀ : i₀ ∈ H) (hv₀ : v i₀ ≠ 0) :
    ∃ (κ : Type u) (_ : Fintype κ) (b : Module.Basis κ K V) (σ : κ → ι) (j₀ : κ),
      (∀ j, σ j ∈ H) ∧ (∀ j, v (σ j) = b j) ∧ σ j₀ = i₀ := by
  have hli : LinearIndepOn K id {v i₀} := (linearIndepOn_singleton_iff K).mpr hv₀
  have hsub : ({v i₀} : Set V) ⊆ v '' H := Set.singleton_subset_iff.mpr ⟨i₀, hi₀, rfl⟩
  have ht : ⊤ ≤ Submodule.span K (v '' H) := hspan.symm.le
  let κ := hli.extend hsub
  let b : Module.Basis κ K V := Module.Basis.extendLe hli hsub ht
  let : Finite κ := Module.Finite.finite_basis b
  let : Fintype κ := Fintype.ofFinite κ
  have hmarked : v i₀ ∈ Set.range b :=
    Module.Basis.subset_extendLe hli hsub ht (Set.mem_singleton _)
  obtain ⟨j₀, hj₀⟩ := hmarked
  have hchoices (j : κ) : ∃ i ∈ H, v i = b j :=
    Module.Basis.extendLe_subset hli hsub ht (Set.mem_range_self j)
  choose σ hσ hσv using hchoices
  refine ⟨κ, inferInstance, b, Function.update σ j₀ i₀, j₀, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = j₀
    · subst j
      simpa only [Function.update_self] using hi₀
    · simpa only [Function.update_of_ne hj] using hσ j
  · intro j
    by_cases hj : j = j₀
    · subst j
      simpa only [Function.update_self] using hj₀.symm
    · simpa only [Function.update_of_ne hj] using hσv j
  · exact Function.update_self _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisWithMarkedLabel
