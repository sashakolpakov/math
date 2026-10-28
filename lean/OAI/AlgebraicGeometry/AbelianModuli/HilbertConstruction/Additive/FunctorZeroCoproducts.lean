import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSections
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functor Zero Coproducts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorZeroCoproducts

noncomputable section

/-! An additive functor to modules sends a finite coproduct to zero when every summand is sent to zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v w

theorem additive_functor_zero_coproduct {C : Type v} [Category.{w} C] [Preadditive C]
    {R : Type u} [CommRing R] (F : C ⥤ ModuleCat.{u} R) [F.Additive]
    {ι : Type u} [Finite ι] (M : ι → C) [HasCoproduct M]
    (hM : ∀ i, IsZero (F.obj (M i))) : IsZero (F.obj (∐ M)) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : HasBiproduct M := HasBiproduct.of_hasCoproduct M
  let : HasBiproduct (F.obj ∘ M) := HasBiproduct.of_hasProduct (F.obj ∘ M)
  let : PreservesBiproduct M F := by
    constructor
    intro b hb
    refine ⟨isBilimitOfTotal _ ?_⟩
    change (∑ i : ι, F.map (b.π i) ≫ F.map (b.ι i)) = 𝟙 (F.obj b.pt)
    calc
      _ = ∑ i : ι, F.map (b.π i ≫ b.ι i) :=
        Finset.sum_congr rfl (fun i _ ↦ (F.map_comp (b.π i) (b.ι i)).symm)
      _ = F.map (∑ i : ι, b.π i ≫ b.ι i) := by rw [F.map_sum]
      _ = F.map (𝟙 b.pt) := congrArg F.map (IsBilimit.total hb)
      _ = 𝟙 (F.obj b.pt) := F.map_id b.pt
  let e : F.obj (∐ M) ≅ ModuleCat.of R (∀ i, F.obj (M i)) :=
    F.mapIso (biproduct.isoCoproduct M).symm ≪≫ F.mapBiproduct M ≪≫
      biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)
  let (i : ι) : Subsingleton (F.obj (M i)) := ModuleCat.subsingleton_of_isZero (hM i)
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (∀ i, F.obj (M i)))).of_iso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorZeroCoproducts
