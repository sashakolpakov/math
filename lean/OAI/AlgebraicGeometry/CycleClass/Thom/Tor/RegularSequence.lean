import OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularQuotient
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Regular Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularSequence

noncomputable section

/-! A sequence regular on an input and on its tensor product preserves
Tor independence after quotienting by the actual generated ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct Pointwise
set_option backward.isDefEq.respectTransparency false

namespace Constructions

universe u
variable (R : Type u) [CommRing R]

theorem higherTor_quotient_sequence_isZero (M N : ModuleCat.{u} R) (rs : List R)
    (hr : IsWeaklyRegular M rs) (ht : IsWeaklyRegular (M ⊗[R] N) rs)
    (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj N)) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj
      (ModuleCat.of R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)))).obj N) := by
  induction rs generalizing M with
  | nil =>
    let e := Submodule.quotEquivOfEqBot (R := R) (M := M)
      (Ideal.ofList [] • ⊤ : Submodule R M) (by
        rw [Ideal.ofList_nil (R := R)]
        exact Submodule.bot_smul (R := R) (A := R) (⊤ : Submodule R M))
    exact (hv n).of_iso (((Tor (ModuleCat R) (n + 1)).mapIso e.toModuleIso).app N)
  | cons r rs ih =>
    obtain ⟨hr, hr'⟩ := (isWeaklyRegular_cons_iff M r rs).mp hr
    obtain ⟨ht, ht'⟩ := (isWeaklyRegular_cons_iff (M ⊗[R] N) r rs).mp ht
    let M' := ModuleCat.of R (QuotSMulTop r M)
    have hT : IsWeaklyRegular (M' ⊗[R] N) rs :=
      ((QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop r N M).isWeaklyRegular_congr rs).mpr ht'
    have hV (i : ℕ) : IsZero (((Tor (ModuleCat R) (i + 1)).obj M').obj N) :=
      RegularQuotient.Constructions.higherTor_quotient_isZero R M N r hr ht hv i
    have h := ih M' hr' hT hV
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs
    exact h.of_iso (((Tor (ModuleCat R) (n + 1)).mapIso e.toModuleIso).app N)

theorem higherTor_regular_quotient_isZero (N : ModuleCat.{u} R) (rs : List R)
    (hr : IsWeaklyRegular R rs) (hn : IsWeaklyRegular N rs) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj N) := by
  have ht : IsWeaklyRegular ((ModuleCat.of R R) ⊗[R] N) rs :=
    ((TensorProduct.lid R N).isWeaklyRegular_congr rs).mpr hn
  have hv (i : ℕ) : IsZero (((Tor (ModuleCat R) (i + 1)).obj (ModuleCat.of R R)).obj N) :=
    TorAlgebra.Flat.Tor.higherTor_isZero R (ModuleCat.of R R) N i
  have h := higherTor_quotient_sequence_isZero R (ModuleCat.of R R) N rs hr ht hv n
  have he : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    change Ideal.ofList rs * (⊤ : Ideal R) = Ideal.ofList rs
    exact Ideal.mul_top (Ideal.ofList rs)
  rw [he] at h
  exact h

theorem euler_regular_quotient_eq_length (N : ModuleCat.{u} R) (rs : List R)
    (hr : IsWeaklyRegular R rs) (hn : IsWeaklyRegular N rs) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj
        (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj N)).toNat) =
      (Module.length R (N ⧸ (Ideal.ofList rs • ⊤ : Submodule R N))).toNat := by
  have hv (i : ℕ) : Module.length R (((Tor (ModuleCat R) (i + 1)).obj
      (ModuleCat.of R (R ⧸ Ideal.ofList rs))).obj N) = 0 := by
    let := ModuleCat.subsingleton_of_isZero (higherTor_regular_quotient_isZero R N rs hr hn i)
    exact Module.length_eq_zero
  have hlen : Module.length R ((R ⧸ Ideal.ofList rs) ⊗[R] N) =
      Module.length R (N ⧸ (Ideal.ofList rs • ⊤ : Submodule R N)) :=
    (TensorProduct.quotTensorEquivQuotSMul N (Ideal.ofList rs)).length_eq
  rw [Finset.sum_range_succ']
  simp [hv, TorAlgebra.Flat.Tor.torZero_length, hlen]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularSequence
