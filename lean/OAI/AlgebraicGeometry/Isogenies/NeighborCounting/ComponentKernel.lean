import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Component Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentKernel.Lifts

/-!
The kernel of a component map from a finite flat group to an etale group
is finite flat. Flatness is proved by cancellation against an etale map:
its diagonal is an open immersion and hence flat.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

theorem flat_map_to_etale {S : Scheme.{u}} {A E : Over S}
    [Flat A.hom] [Etale E.hom] (f : A ⟶ E) : Flat f.left := by
  have : MorphismProperty.HasOfPostcompProperty (@Flat : MorphismProperty Scheme.{u}) @Etale := by
    erw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y g hg
    have : Etale g := hg
    exact inferInstanceAs (Flat (pullback.diagonal g))
  have hf : Flat (f.left ≫ E.hom) := (congrArg Flat f.w).mpr inferInstance
  exact MorphismProperty.of_postcomp (@Flat : MorphismProperty Scheme.{u}) f.left E.hom
    (inferInstance : Etale E.hom) hf

variable {S : Scheme.{u}} {A E : Over S} [GrpObj A] [GrpObj E]
variable [IsFinite A.hom] [Flat A.hom] [Etale E.hom] [IsSeparated E.hom]
variable (π : A ⟶ E) [IsMonHom π]

omit [GrpObj A] [GrpObj E] [Flat A.hom] [Etale E.hom] [IsMonHom π] in
theorem componentMap_finite : IsFinite π.left := by
  have : IsFinite (π.left ≫ E.hom) := (congrArg IsFinite π.w).mpr inferInstance
  exact IsFinite.of_comp π.left E.hom

omit [GrpObj A] [IsMonHom π] in
/-- The identity component is the actual scheme-theoretic kernel, with
its finite flat geometry derived from the source and etale component map. -/
theorem componentKernel_finite_flat :
    IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject π).hom ∧ Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject π).hom := by
  have : IsFinite π.left := componentMap_finite π
  have : Flat π.left := flat_map_to_etale π
  exact ⟨Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite π, Picard.PoincareBundle.Kernel.Scheme.kernel_flat π⟩

omit [GrpObj A] [Flat A.hom] [IsMonHom π] in
theorem componentKernel_finitePresentation [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject π).hom := by
  have : IsFinite π.left := componentMap_finite π
  have : IsLocallyNoetherian E.left := LocallyOfFiniteType.isLocallyNoetherian E.hom
  have : LocallyOfFinitePresentation π.left := inferInstance
  rw [Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd]
  exact MorphismProperty.of_isPullback (Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback π)
    (inferInstance : LocallyOfFinitePresentation π.left)

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentKernel.Lifts
