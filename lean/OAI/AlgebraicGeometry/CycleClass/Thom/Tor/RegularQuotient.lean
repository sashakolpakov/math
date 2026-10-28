import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Linear
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # Regular Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularQuotient

noncomputable section

/-! Quotienting one input by an element regular on that input and on
the tensor product preserves the vanishing of all higher native Tor modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace Constructions

universe u
variable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (r : R)

theorem higherTor_quotient_isZero (hr : IsSMulRegular M r)
    (ht : IsSMulRegular (M ⊗[R] N) r)
    (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N)) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R (QuotSMulTop r M))).obj N) := by
  let S := M.smulShortComplex r
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact hr
  have hδ : TorAlgebra.ExactSequence.Tor.connecting R N S hS n = 0 := by
    cases n with
    | zero =>
      let F := (Tor (ModuleCat R) 0).flip.obj N
      have hf : Mono (((Tor (ModuleCat R) 0).map S.f).app N) := by
        change Mono (F.map (r • 𝟙 M))
        rw [Functor.map_smul, F.map_id, ModuleCat.mono_iff_injective]
        exact ((TorAlgebra.Flat.Tor.torZeroIso R M N).toLinearEquiv.isSMulRegular_congr r).mpr ht
      apply (cancel_mono (((Tor (ModuleCat R) 0).map S.f).app N)).mp
      rw [zero_comp]
      exact TorAlgebra.ExactSequence.Tor.connecting_comp R N S hS 0
    | succ n => exact (hv n).eq_zero_of_tgt _
  exact (TorAlgebra.ExactSequence.Tor.exact_before_connecting R N S hS n).isZero_of_both_zeros
    ((hv n).eq_zero_of_src _) hδ

theorem higherTor_quotient_right_isZero (hr : IsSMulRegular N r)
    (ht : IsSMulRegular (M ⊗[R] N) r)
    (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N)) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj (ModuleCat.of R (QuotSMulTop r N))) := by
  have ht' : IsSMulRegular (N ⊗[R] M) r :=
    ((TensorProduct.comm R N M).isSMulRegular_congr r).mpr ht
  have hv' (n : ℕ) : IsZero (((Tor (ModuleCat R) (n + 1)).obj N).obj M) :=
    (hv n).of_iso (TorAlgebra.Symmetry.Tor.iso R N M (n + 1))
  exact (higherTor_quotient_isZero R N M r hr ht' hv' n).of_iso
    (TorAlgebra.Symmetry.Tor.iso R M (ModuleCat.of R (QuotSMulTop r N)) (n + 1))

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularQuotient
