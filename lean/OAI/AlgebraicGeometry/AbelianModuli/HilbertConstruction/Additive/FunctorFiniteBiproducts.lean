import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functor Finite Biproducts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteBiproducts

noncomputable section

/-! Explicit finite-biproduct preservation for additive functors, without restricting the universe of the finite index type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w z i

theorem additive_functor_preserves_finite_biproduct
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {I : Type i} [Fintype I] (M : I → C) : PreservesBiproduct M F := by
  constructor
  intro b hb
  refine ⟨isBilimitOfTotal _ ?_⟩
  change (∑ j : I, F.map (b.π j) ≫ F.map (b.ι j)) = 𝟙 (F.obj b.pt)
  calc
    _ = ∑ j : I, F.map (b.π j ≫ b.ι j) :=
      Finset.sum_congr rfl (fun j _ => (F.map_comp (b.π j) (b.ι j)).symm)
    _ = F.map (∑ j : I, b.π j ≫ b.ι j) := by rw [F.map_sum]
    _ = F.map (𝟙 b.pt) := congrArg F.map (IsBilimit.total hb)
    _ = 𝟙 (F.obj b.pt) := F.map_id b.pt

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteBiproducts
