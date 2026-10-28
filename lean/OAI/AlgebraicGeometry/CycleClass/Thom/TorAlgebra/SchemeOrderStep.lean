import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder

/-! # Scheme Order Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep

noncomputable section

/-! Regular intersection devissage with the exact Scheme.ord
coefficients of the actual affine source rational function. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep
open OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (r : R)

omit [IsNoetherianRing R] in
theorem equation_image_ne_zero (hn : IsSMulRegular (R ⧸ P) r) :
    algebraMap R (R ⧸ P) r ≠ 0 := by
  intro hz
  change Function.Injective (fun x : R ⧸ P => r • x) at hn
  have he : r • (1 : R ⧸ P) = r • (0 : R ⧸ P) := by
    rw [← algebraMap_smul (R ⧸ P) r, hz, zero_smul, smul_zero]
  exact one_ne_zero (hn he)

theorem source_prime_height_one (p : SourceOrderStep.ResidualComponent R P r) (hn : IsSMulRegular (R ⧸ P) r) :
    (SourceOrderStep.residualSourcePrime R P r p).asIdeal.height = 1 :=
  ResidualMinimalSourcePrime.Constructions.minimalSourcePrime_height_one R P r p.val
    ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p.val).mp p.property)
    (mem_nonZeroDivisors_of_ne_zero (equation_image_ne_zero R P r hn))

theorem source_schemeOrder (p : SourceOrderStep.ResidualComponent R P r) (hn : IsSMulRegular (R ⧸ P) r) :
    (Spec (CommRingCat.of (R ⧸ P))).ord (Affine.PrincipalSchemeOrder.Constructions.affineFunction (R ⧸ P) (algebraMap R (R ⧸ P) r))
      (SourceOrderStep.residualSourcePrime R P r p) =
      ((Ring.ord (Localization.AtPrime (SourceOrderStep.residualSourcePrime R P r p).asIdeal)
        (algebraMap (R ⧸ P) (Localization.AtPrime (SourceOrderStep.residualSourcePrime R P r p).asIdeal)
          (algebraMap R (R ⧸ P) r))).toNat : ℤ) :=
  Affine.PrincipalSchemeOrder.Constructions.schemeOrder_eq_localOrder (R ⧸ P) (SourceOrderStep.residualSourcePrime R P r p)
    (source_prime_height_one R P r p hn) _ (equation_image_ne_zero R P r hn)

variable [IsLocalRing R] (rs : List R)
  (hr : IsWeaklyRegular R (r :: rs))
  (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R)
  (hn : IsSMulRegular (R ⧸ P) r)
  (hd : Module.supportDim R (R ⧸ P) ≤ ((r :: rs).length : WithBot ℕ∞))
  (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R (R ⧸ P) ⊆
    {IsLocalRing.closedPoint R})

include hr hm hn hd hi

theorem euler_eq_source_schemeOrder_sum (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) (ModuleCat.of R (R ⧸ P)) d =
      ∑ p : SourceOrderStep.ResidualComponent R P r,
        ((Spec (CommRingCat.of (R ⧸ P))).ord
          (Affine.PrincipalSchemeOrder.Constructions.affineFunction (R ⧸ P) (algebraMap R (R ⧸ P) r)) (SourceOrderStep.residualSourcePrime R P r p) : ℚ) *
          Euler.Tor.euler (R ⧸ Ideal.span {r})
            (ModuleCat.of (R ⧸ Ideal.span {r})
              ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
            (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ p.val.asIdeal)) d := by
  rw [SourceOrderStep.euler_eq_source_order_sum R P r rs hr hm hn hd hi d hD]
  apply Finset.sum_congr rfl
  intro p _
  rw [source_schemeOrder R P r p hn, Int.cast_natCast]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep
