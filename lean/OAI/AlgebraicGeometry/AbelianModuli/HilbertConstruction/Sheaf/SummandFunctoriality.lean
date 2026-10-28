import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands

/-! # Summand Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandFunctoriality

noncomputable section

/-! Split image sheaves are preserved by every functor between module-sheaf categories, hence in particular by arbitrary scheme pullback. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) {M : X.Modules}

def sheafSummandFunctorMap (p : End M) :
    F.obj (IdempotentSheafSummands.idempotentSheafSummand p) ⟶ IdempotentSheafSummands.idempotentSheafSummand (F.map p) :=
  equalizer.lift (F.map (IdempotentSheafSummands.idempotentSheafInclusion p)) (by
    rw [Category.comp_id, ← F.map_comp, IdempotentSheafSummands.idempotentSheafInclusion_fixed])

theorem sheafSummandFunctorMap_inclusion (p : End M) :
    sheafSummandFunctorMap F p ≫ IdempotentSheafSummands.idempotentSheafInclusion (F.map p) =
      F.map (IdempotentSheafSummands.idempotentSheafInclusion p) := equalizer.lift_ι _ _

def sheafSummandFunctorIso (p : End M) (hp : p ≫ p = p) :
    F.obj (IdempotentSheafSummands.idempotentSheafSummand p) ≅ IdempotentSheafSummands.idempotentSheafSummand (F.map p) where
  hom := sheafSummandFunctorMap F p
  inv := IdempotentSheafSummands.idempotentSheafInclusion (F.map p) ≫ F.map (IdempotentSheafSummands.idempotentSheafRetraction p hp)
  hom_inv_id := by
    rw [← Category.assoc, sheafSummandFunctorMap_inclusion, ← F.map_comp,
      IdempotentSheafSummands.idempotentSheafInclusion_retraction, F.map_id]
  inv_hom_id := by
    apply (cancel_mono (IdempotentSheafSummands.idempotentSheafInclusion (F.map p))).mp
    rw [Category.assoc, sheafSummandFunctorMap_inclusion, Category.assoc,
      ← F.map_comp, IdempotentSheafSummands.idempotentSheafRetraction_inclusion,
      IdempotentSheafSummands.idempotentSheafInclusion_fixed, Category.id_comp]

def sheafSummandPullbackIso (f : Y ⟶ X) (p : End M) (hp : p ≫ p = p) :
    (Scheme.Modules.pullback f).obj (IdempotentSheafSummands.idempotentSheafSummand p) ≅
      IdempotentSheafSummands.idempotentSheafSummand ((Scheme.Modules.pullback f).map p) :=
  sheafSummandFunctorIso _ p hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandFunctoriality
