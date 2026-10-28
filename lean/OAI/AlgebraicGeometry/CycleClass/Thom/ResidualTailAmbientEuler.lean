import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ElementChangeOfRings
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Residual Tail Ambient Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualTailAmbientEuler.Constructions

noncomputable section

/-! The residual tail Tor calculation can be returned to the original
ambient ring. The needed independence follows from permutation of the
actual regular sequence over the local Noetherian ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct Pointwise

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentLength.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ElementChangeOfRings.Regular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (r : R) (rs : List R)
  (hr : IsWeaklyRegular R (r :: rs))
  (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal R)

include hr hm

theorem regular_on_tail_quotient : IsSMulRegular (R ⧸ Ideal.ofList rs) r := by
  have hp : (r :: rs).Perm (rs ++ [r]) :=
    show ([r] ++ rs).Perm (rs ++ [r]) from List.perm_append_comm
  have h := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hr hp hm
  have ht := ((isWeaklyRegular_append_iff R rs [r]).mp h).2
  have he : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    change Ideal.ofList rs * (⊤ : Ideal R) = Ideal.ofList rs
    exact Ideal.mul_top _
  rw [he] at ht
  exact (isWeaklyRegular_singleton_iff _ r).mp ht

theorem regular_tail_ambient : IsWeaklyRegular R rs := by
  have hp : (r :: rs).Perm (rs ++ [r]) :=
    show ([r] ++ rs).Perm (rs ++ [r]) from List.perm_append_comm
  exact ((isWeaklyRegular_append_iff R rs [r]).mp
    (IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hr hp hm)).1

omit hr hm [IsNoetherianRing R] [IsLocalRing R] in
def tailBaseChangeIso :
    ModuleCat.of (R ⧸ Ideal.span {r})
      ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})) )) ≅
    (TorAlgebra.FlatExtension.baseChange R (R ⧸ Ideal.span {r})).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  ((Ideal.quotientEquivAlgOfEq (R ⧸ Ideal.span {r})
    (Ideal.map_ofList (algebraMap R (R ⧸ Ideal.span {r})) rs).symm).toLinearEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R ⧸ Ideal.span {r}) (Ideal.ofList rs)).toLinearEquiv).toModuleIso

theorem residual_tail_euler_eq_ambient (M : ModuleCat.{u} (R ⧸ Ideal.span {r})) (d : ℕ) :
    TorAlgebra.Euler.Tor.euler (R ⧸ Ideal.span {r})
      (ModuleCat.of (R ⧸ Ideal.span {r})
        ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r}))))) M d =
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs))
      ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {r}))).obj M) d := by
  let S := R ⧸ Ideal.span {r}
  let N := ModuleCat.of R (R ⧸ Ideal.ofList rs)
  have hhead := ((isWeaklyRegular_cons_iff R r rs).mp hr).1
  have hv := TorAlgebra.ElementChangeOfRings.Regular.quotient_tor_isZero R r N hhead (regular_on_tail_quotient R r rs hr hm)
  exact (TorAlgebra.EulerTransport.Tor.comm S _ M d).trans
    ((TorAlgebra.EulerTransport.Tor.iso_right S M (tailBaseChangeIso R r rs) d).trans
      ((TorAlgebra.IndependentLength.Tor.euler_eq R S M N Ideal.Quotient.mk_surjective hv d).trans
        (TorAlgebra.EulerTransport.Tor.comm R _ N d)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualTailAmbientEuler.Constructions
