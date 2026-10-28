import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LeftBoundEuler
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Excess Sequence Left Bound -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExcessSequenceLeftBound

noncomputable section

/-! Further regular equations give zero native Tor Euler characteristic
after support isolation, using only the final regular quotient's bound.
No projective-dimension bound is required on the second module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped Pointwise

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N] (d : ℕ)

theorem euler_sequence_eq_zero (M : ModuleCat.{u} R) [Module.Finite R M]
    (rs : List R) (hr : IsWeaklyRegular M rs) (hne : rs ≠ [])
    [HasProjectiveDimensionLE (ModuleCat.of R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) d]
    (x : PrimeSpectrum R) (hx : Module.support R M ∩ Module.support R N ⊆ {x}) :
    Euler.Tor.euler R (ModuleCat.of R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) N d = 0 := by
  induction rs generalizing M with
  | nil => exact (hne rfl).elim
  | cons r rs ih =>
    obtain ⟨hr0, hr'⟩ := (isWeaklyRegular_cons_iff M r rs).mp hr
    by_cases ht : rs = []
    · subst rs
      let e := Submodule.quotEquivOfEq (R := R) (M := M)
        (Ideal.ofList [r] • ⊤ : Submodule R M) (r • ⊤)
        (by rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul])
      let : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r M)) d :=
        hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)
      exact (IsolatedEuler.euler_iso_left R e.toModuleIso N d).trans
        (LeftBoundEuler.euler_quotient_eq_zero R N d M r hr0 x hx)
    · let M' := ModuleCat.of R (QuotSMulTop r M)
      let : Module.Finite R M' := inferInstanceAs (Module.Finite R (QuotSMulTop r M))
      let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs
      let : HasProjectiveDimensionLE (ModuleCat.of R (M' ⧸ (Ideal.ofList rs • ⊤ : Submodule R M'))) d :=
        hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)
      have hs : Module.support R M' ⊆ Module.support R M :=
        Module.support_subset_of_surjective (r • (⊤ : Submodule R M)).mkQ (Submodule.mkQ_surjective _)
      have hi := ih M' hr' ht ((Set.inter_subset_inter_left _ hs).trans hx)
      exact (IsolatedEuler.euler_iso_left R e.toModuleIso N d).trans hi

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExcessSequenceLeftBound
