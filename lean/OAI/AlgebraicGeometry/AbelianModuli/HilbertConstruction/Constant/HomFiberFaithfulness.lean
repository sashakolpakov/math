import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.HomFiberDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects

/-! # Hom Fiber Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A single field-valued fiber distinguishes homomorphisms of constant abelian families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K F : Type u} [Field K] [Field F] {g h : ℕ} {T : Scheme.{u}}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
variable (t : T ⟶ Spec (.of K)) [PreconnectedSpace T] (s : Spec (.of F) ⟶ T)

theorem Abelian.Schemes.AbelianScheme.pullback_hom_eq_of_field_fiber
    (f q : (A.pullback t).scheme ⟶ (B.pullback t).scheme) [IsMonHom f] [IsMonHom q]
    (hfq : (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  have : IsMonHom (f / q) := by
    let d : (A.pullback t).groupObject ⟶ (B.pullback t).groupObject := Grp.homMk f / Grp.homMk q
    exact inferInstanceAs (IsMonHom d.hom.hom)
  apply div_eq_one.mp
  apply A.pullback_hom_eq_one_of_field_fiber B t (f / q) s
  rw [div_eq_mul_inv, Functor.map_mul, Functor.map_inv', hfq, mul_inv_cancel]

theorem Abelian.Schemes.AbelianScheme.pullback_groupHom_field_fiber_injective :
    Function.Injective (fun f : (A.pullback t).groupObject ⟶ (B.pullback t).groupObject =>
      (Over.pullback s).map f.hom.hom) := by
  intro f q hfq
  exact Grp.hom_ext _ _ (A.pullback_hom_eq_of_field_fiber B t s f.hom.hom q.hom.hom hfq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
