import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomDivisionUniqueness
import Mathlib.Algebra.Module.Torsion.Free

/-! # Hom Torsion Free -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomTorsionFree

noncomputable section

/-! The additive group of abelian-variety homomorphisms into a polarized target is torsion-free over the integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))

instance polarized_groupHom_torsionFree :
    IsMulTorsionFree (B.groupObject ⟶ A.abelian.groupObject) where
  pow_left_injective {n} hn f k hfk := by
    apply Grp.hom_ext f k
    have h : f.hom.hom ^ n = k.hom.hom ^ n := by
      have he := congrArg (fun e : B.groupObject ⟶ A.abelian.groupObject => e.hom.hom) hfk
      simpa only [Grp.Hom.hom_pow, Mon.Hom.hom_pow] using he
    exact HomDivisionUniqueness.polarized_hom_pow_injective A B f.hom.hom k.hom.hom n (Nat.pos_of_ne_zero hn) h

theorem polarized_addHom_isAddTorsionFree : IsAddTorsionFree (B.AddHom A.abelian) := inferInstance

theorem polarized_addHom_isTorsionFree : Module.IsTorsionFree ℤ (B.AddHom A.abelian) := inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.HomTorsionFree
