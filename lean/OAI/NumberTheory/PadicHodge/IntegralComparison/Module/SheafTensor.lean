import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Sheaf Tensor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafTensor

noncomputable section

/-! Sheafification of module presheaves is compatible with tensor
products on every site whose objects and morphisms fit in the native
module universe. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonoidalClosed

universe u v

theorem monoidal {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] :
    (J.W (A := ModuleCat.{max u v} R)).IsMonoidal := by
  let : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{max u v, max u v, max u v, max u v} (R := R)
  let : ∀ (F G : Cᵒᵖ ⥤ ModuleCat.{max u v} R),
      Enriched.FunctorCategory.HasEnrichedHom (ModuleCat.{max u v} R) F G := by
    intro F G
    change HasEnd _
    infer_instance
  let : ∀ (F G : Cᵒᵖ ⥤ ModuleCat.{max u v} R),
      Enriched.FunctorCategory.HasFunctorEnrichedHom (ModuleCat.{max u v} R) F G := by
    intro F G U
    change HasEnd _
    infer_instance
  exact GrothendieckTopology.W.monoidal

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafTensor
