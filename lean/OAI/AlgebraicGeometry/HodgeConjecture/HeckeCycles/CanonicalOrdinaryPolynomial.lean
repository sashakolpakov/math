import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointwiseOrdinaryPolynomial

/-! # Canonical Ordinary Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CanonicalOrdinaryPolynomial.CM.Ordinary

noncomputable section

/-! The genuine prime-field algebraic Frobenius satisfies the Hecke
polynomial on every ordinary Albanese difference, conditional only on
the literal reduced-neighbor formulas at this stage. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)
local notation "aκ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a

theorem polynomial_annihilates_actual_ordinary_differences
    (hs : Smooth (M.integral a).toOver.hom)
    (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Z : Intrinsic.Detection.CM.ordinaryPoints R a → Intrinsic.Detection.CM.ordinaryPoints R a)
    (Y : Intrinsic.Detection.CM.ordinaryPoints R a → Multiset (Intrinsic.Detection.CM.ordinaryPoints R a))
    (hH : ∀ (i : Fin 3) (x y : Intrinsic.Detection.CM.ordinaryPoints R a), x.1 = y.1 →
      act (H i) (aκ x - aκ y) =
        ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y i x).map aκ).sum -
          ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y i y).map aκ).sum)
    (x y : Intrinsic.Detection.CM.ordinaryPoints R a) (hxy : x.1 = y.1) :
    act (Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H) (aκ x - aκ y) = 0 :=
  PointwiseOrdinaryPolynomial.CM.Ordinary.polynomial_annihilates_differences q act
    (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
    (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H
    (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y (Ordinary.PointFrobenius.CM.ordinaryFrobenius_component R a hs)
    (SpecialOrdinaryFrobenius.CM.Ordinary.algebraicFrobenius_on_ordinaryImage R a hs) hH x y hxy

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CanonicalOrdinaryPolynomial.CM.Ordinary
