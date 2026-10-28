import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Faithfully Flat Tensor Epi -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi

noncomputable section

/-! Products of faithfully flat maps over the base are epimorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

theorem over_tensor_epi_of_flat_surjective {S : Scheme.{u}} {X Y Z W : Over S}
    (f : X ⟶ Y) (g : Z ⟶ W) [Flat f.left] [Surjective f.left]
    [Flat g.left] [Surjective g.left] : Epi (f ⊗ₘ g) := by
  have : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective.{u}) :=
    { comp_mem := fun _ _ ha hb => ⟨hb.1.comp ha.1⟩ }
  have : Flat (f ⊗ₘ g).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance f.w.symm g.w.symm
  have : Surjective (f ⊗ₘ g).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Surjective.{u}) inferInstance inferInstance f.w.symm g.w.symm
  have : Epi ((Over.forget S).map (f ⊗ₘ g)) := Flat.epi_of_flat_of_surjective (f ⊗ₘ g).left
  exact Functor.epi_of_epi_map (Over.forget S) inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfullyFlatTensorEpi
