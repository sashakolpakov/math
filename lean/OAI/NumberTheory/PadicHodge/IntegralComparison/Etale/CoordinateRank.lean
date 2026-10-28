import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Coordinate Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateRank

noncomputable section

/-! Étale coordinate differentials have a basis of the geometric rank,
computed at any actual point of the affine chart. -/

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype σ] [Algebra (MvPolynomial σ R) A]
  [IsScalarTower R (MvPolynomial σ R) A] [Algebra.Etale (MvPolynomial σ R) A]
  (p : PrimeSpectrum A) (g : ℕ) (hg : Module.rankAtStalk Ω[A⁄R] p = g)

include hg in
theorem card : Fintype.card σ = g := by
  let b := CoordinateFormBasis.kaehlerBasis R A σ
  let : Module.Free A Ω[A⁄R] := Module.Free.of_basis b
  let : Nontrivial A := p.nontrivial
  exact (Module.finrank_eq_card_basis b).symm.trans
    (((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := A) (M := Ω[A⁄R])) p).symm).trans hg)

def basis : Module.Basis (Fin g) A Ω[A⁄R] :=
  (CoordinateFormBasis.kaehlerBasis R A σ).reindex
    ((Fintype.equivFin σ).trans (finCongr (CoordinateRank.card R A σ p g hg)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateRank
