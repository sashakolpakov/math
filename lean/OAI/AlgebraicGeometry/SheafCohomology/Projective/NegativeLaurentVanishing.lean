import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop

/-! # Negative Laurent Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentVanishing

noncomputable section

open _root_.MvPolynomial

/-! Positive Laurent Čech cohomology vanishes away from the top cover degree. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateFullNegativeCochain_eq_zero_of_card_ne (d : ℤ) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card σ)
    (s : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u} (R := R) (σ := σ) d n) : s = 0 := by
  funext e
  have hN (N : Set (ULift.{u} σ)) (hN : N = Set.univ)
      (z : OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of R), ⊤) N n) : z = 0 := by
    subst N
    exact OrderedCechSupport.orderedCechFullSupport_eq_zero_of_card_ne Γ(Spec (CommRingCat.of R), ⊤) n
      (by simpa using hn) z
  exact hN e.val.liftedNegativeSupport e.property (s e)

theorem coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_card_ne
    (j : σ) (d : ℤ) (n : ℕ) (hn : n + 2 ≠ Fintype.card σ) :
    Subsingleton ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1)) := by
  have : Subsingleton (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u}
      (R := R) (σ := σ) d (n + 1)) :=
    ⟨fun x y => (coordinateFullNegativeCochain_eq_zero_of_card_ne (R := R) d (n + 1) hn x).trans
      (coordinateFullNegativeCochain_eq_zero_of_card_ne (R := R) d (n + 1) hn y).symm⟩
  exact ((NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n).trans
    (NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCyclesEquivCochain (R := R) d (n + 1))).injective.subsingleton

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentVanishing
