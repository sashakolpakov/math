import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedComponentFiniteness

/-! # Component Constant Finite Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentConstantFiniteImage

noncomputable section

/-! Constancy on every reduced irreducible component gives a finite underlying image for a morphism from a noetherian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsNoetherian X]

theorem finite_range_of_constant_reduced_components (p : X ⟶ Spec (.of K)) (f : X ⟶ Y)
    (h : ∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
      ∃ a : Spec (.of K) ⟶ Y,
        (ReducedClosedSubschemes.reducedClosedInclusion X ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ ≫ p) ≫ a =
          ReducedClosedSubschemes.reducedClosedInclusion X ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ ≫ f) :
    (Set.range f).Finite := by
  have himg (C : Set X) (hC : C ∈ irreducibleComponents X) : (f '' C).Finite := by
    let Z : TopologicalSpace.Closeds X := ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
    let i := ReducedClosedSubschemes.reducedClosedInclusion X Z
    obtain ⟨a, ha⟩ := h C hC
    apply (Set.finite_range a).subset
    rintro y ⟨x, hx, rfl⟩
    have hi : x ∈ Set.range i := (ReducedClosedSubschemes.reducedClosedInclusion_range X Z).symm ▸ hx
    obtain ⟨w, hw⟩ := hi
    refine ⟨(i ≫ p) w, ?_⟩
    have hv := congrArg (fun b : ReducedClosedSubschemes.reducedClosedSubscheme X Z ⟶ Y => b w) ha
    change a ((i ≫ p) w) = f (i w) at hv
    exact hv.trans (congrArg f hw)
  rw [← Set.image_univ, ← sUnion_irreducibleComponents (X := X), Set.image_sUnion, Set.sUnion_image]
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.biUnion himg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentConstantFiniteImage
