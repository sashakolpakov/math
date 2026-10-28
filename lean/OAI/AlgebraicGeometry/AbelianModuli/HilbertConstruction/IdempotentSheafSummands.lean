import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Idempotent Sheaf Summands -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands

noncomputable section

/-! An idempotent on a module sheaf has an actual equalizer summand, with an explicit inclusion and retraction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {M : X.Modules}

def idempotentSheafSummand (p : End M) : X.Modules := equalizer (𝟙 M) p

def idempotentSheafInclusion (p : End M) : idempotentSheafSummand p ⟶ M :=
  equalizer.ι (𝟙 M) p

def idempotentSheafRetraction (p : End M) (hp : p ≫ p = p) : M ⟶ idempotentSheafSummand p :=
  equalizer.lift p (by rw [Category.comp_id, hp])

instance (p : End M) : Mono (idempotentSheafInclusion p) :=
  inferInstanceAs (Mono (equalizer.ι (𝟙 M) p))

theorem idempotentSheafInclusion_fixed (p : End M) :
    idempotentSheafInclusion p ≫ p = idempotentSheafInclusion p :=
  (equalizer.condition (𝟙 M) p).symm.trans (Category.comp_id _)

theorem idempotentSheafRetraction_inclusion (p : End M) (hp : p ≫ p = p) :
    idempotentSheafRetraction p hp ≫ idempotentSheafInclusion p = p :=
  equalizer.lift_ι _ _

theorem idempotentSheafInclusion_retraction (p : End M) (hp : p ≫ p = p) :
    idempotentSheafInclusion p ≫ idempotentSheafRetraction p hp = 𝟙 _ := by
  apply (cancel_mono (idempotentSheafInclusion p)).mp
  rw [Category.assoc, idempotentSheafRetraction_inclusion,
    idempotentSheafInclusion_fixed, Category.id_comp]

theorem idempotentSheafInclusion_retraction_orthogonal (p q : End M)
    (hq : q ≫ q = q) (hpq : p ≫ q = 0) :
    idempotentSheafInclusion p ≫ idempotentSheafRetraction q hq = 0 := by
  apply (cancel_mono (idempotentSheafInclusion q)).mp
  rw [Category.assoc, idempotentSheafRetraction_inclusion, zero_comp]
  calc
    idempotentSheafInclusion p ≫ q = (idempotentSheafInclusion p ≫ p) ≫ q := by
      rw [idempotentSheafInclusion_fixed]
    _ = 0 := by rw [Category.assoc, hpq, comp_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdempotentSheafSummands
