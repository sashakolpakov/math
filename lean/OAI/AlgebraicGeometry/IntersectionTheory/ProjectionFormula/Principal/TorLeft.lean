import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Tor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Linear

/-! # Tor Left -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.TorLeft

noncomputable section

/-! Native Tor against a regular principal quotient in its first argument.
The proof uses the actual long exact sequence, rather than assuming a
symmetry comparison for the two derived tensor constructions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct Pointwise

universe u

variable (R : Type u) [CommRing R] (r : R)

theorem higherTor_isZero (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R (QuotSMulTop r R))).obj M) := by
  let S := (ModuleCat.of R R).smulShortComplex r
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact hr
  have he := ProjectionFormula.Tor.ExactSequence.exact_before_connecting R M S hS n
  have hfirst : ((Tor (ModuleCat R) (n + 1)).map S.g).app M = 0 :=
    (ProjectionFormula.Tor.Flat.higherTor_isZero R (.of R R) M n).eq_zero_of_src _
  apply he.isZero_of_both_zeros hfirst
  cases n with
  | zero =>
    let F := (Tor (ModuleCat R) 0).flip.obj M
    have hmap : F.map S.f = r • 𝟙 (F.obj (.of R R)) := by
      change F.map (r • 𝟙 (ModuleCat.of R R)) = _
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have hmono : Mono (F.map S.f) := by
      rw [hmap, ModuleCat.mono_iff_injective]
      let e : F.obj (.of R R) ≃ₗ[R] M :=
        (ProjectionFormula.Tor.Flat.torZeroIso R (.of R R) M).toLinearEquiv.trans (TensorProduct.lid R M)
      exact (e.isSMulRegular_congr r).mpr hm
    let : Mono (((Tor (ModuleCat R) 0).map S.f).app M) := hmono
    apply (cancel_mono (((Tor (ModuleCat R) 0).map S.f).app M)).mp
    rw [ProjectionFormula.Tor.ExactSequence.connecting_comp, zero_comp]
  | succ n =>
    exact (ProjectionFormula.Tor.Flat.higherTor_isZero R (.of R R) M n).eq_zero_of_tgt _

theorem higherTor_length (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) (n + 1)).obj
      (ModuleCat.of R (QuotSMulTop r R))).obj M) = 0 := by
  let := ModuleCat.subsingleton_of_isZero (higherTor_isZero R r hr M hm n)
  exact Module.length_eq_zero

theorem euler_length (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj
        (ModuleCat.of R (QuotSMulTop r R))).obj M)).toNat) =
      (Module.length R (QuotSMulTop r M)).toNat := by
  have hI : (r • (⊤ : Submodule R R) : Ideal R) = Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hlen : Module.length R ((QuotSMulTop r R) ⊗[R] M) =
      Module.length R (QuotSMulTop r M) := by
    change Module.length R ((R ⧸ (r • (⊤ : Submodule R R))) ⊗[R] M) = _
    rw [hI, (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {r})).length_eq,
      Submodule.ideal_span_singleton_smul]
  rw [Finset.sum_range_succ']
  simp [higherTor_length R r hr M hm, ProjectionFormula.Tor.Flat.torZero_length, hlen]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.TorLeft
