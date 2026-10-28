import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialDetection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryPolynomial

/-! # Detected Polynomial -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial.CM

/-! The actual prime-field Frobenius satisfies the Hecke polynomial.
IntegralModel generation and CMPoints density supply detection, while the ordinary
Frobenius action and component preservation are proved from geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)
local notation "aκ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a

theorem polynomial_from_actual_ordinary_formulas
    (hs : Smooth (M.integral a).toOver.hom)
    (hS : ∀ i, Smooth ((M.components a).S i).hom)
    (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
    (hgenerate : ∀ i, ∃ n : ℕ, 0 < n ∧
      ∀ t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base,
        Function.Surjective ((M.components a).sumOfDifferences i n t))
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Z : Intrinsic.Detection.CM.ordinaryPoints R a → Intrinsic.Detection.CM.ordinaryPoints R a)
    (Y : Intrinsic.Detection.CM.ordinaryPoints R a → Multiset (Intrinsic.Detection.CM.ordinaryPoints R a))
    (hH : ∀ (i : Fin 3) (x y : Intrinsic.Detection.CM.ordinaryPoints R a), x.1 = y.1 →
      act (H i) (aκ x - aκ y) =
        ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y i x).map aκ).sum -
          ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y i y).map aκ).sum) :
    Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H = 0 := by
  apply Intrinsic.SpecialDetection.CM.algebraic_detection R a hS hA hgenerate ho hd
  intro x y hxy
  exact SpecialOrdinaryPolynomial.CM.Ordinary.polynomial_annihilates_actual_ordinary_differences R a
    hs H Z Y hH x y hxy

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData

/-! Compact predicates for the literal ordinary formulas and their
Frobenius polynomial, parameterized by operators on the original
Albanese. Their definitions contain no native evaluation-field data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM

def Formulas {S G J : Type} [AddCommGroup G] (q : ℕ)
    (component : S → J) (image : S → G) (X Z : S → S) (Y : S → Multiset S)
    (H : Fin 3 → G → G) : Prop :=
  ∀ (i : Fin 3) (x y : S), component x = component y →
    H i (image x - image y) =
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i x).map image).sum -
        ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i y).map image).sum

def AlgebraFormulas {B S G J : Type} [AddCommGroup G] (q : ℕ)
    (component : S → J) (image : S → G) (act : B → G → G)
    (X Z : S → S) (Y : S → Multiset S) (H : Fin 3 → B) : Prop :=
  Formulas q component image X Z Y (fun i => act (H i))

theorem algebraFormulas_of_formulas {B S G J : Type} [AddCommGroup G] (q : ℕ)
    (component : S → J) (image : S → G) (act : B → G → G)
    (X Z : S → S) (Y : S → Multiset S) (H : Fin 3 → B)
    (h : Formulas q component image X Z Y (fun i => act (H i))) :
    AlgebraFormulas q component image act X Z Y H := h

def Polynomial {B : Type*} [Ring B] (q : ℕ) (Φ : B) (H : Fin 3 → B) : Prop :=
  Polynomial.CM.heckePolynomialValue q Φ H = 0

theorem formulas_congr {S G J : Type} [AddCommGroup G] (q : ℕ)
    (component : S → J) (image : S → G) (X : S → S)
    {Z Z' : S → S} {Y Y' : S → Multiset S} {H H' : Fin 3 → G → G}
    (hZ : Z = Z') (hY : Y = Y') (hH : H = H')
    (h : Formulas q component image X Z Y H) :
    Formulas q component image X Z' Y' H' := by
  subst Z'
  subst Y'
  subst H'
  exact h

theorem polynomial_value {B : Type*} [Ring B] (q : ℕ) (Φ : B) (H : Fin 3 → B)
    (h : Polynomial q Φ H) : Polynomial.CM.heckePolynomialValue q Φ H = 0 := h

theorem polynomial_congr {B : Type*} [Ring B] (q : ℕ) (Φ : B)
    {H H' : Fin 3 → B} (hH : H = H') (h : Polynomial q Φ H) : Polynomial q Φ H' := by
  subst H'
  exact h

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)

theorem polynomial_of_formulas
    (hs : Smooth (M.integral a).toOver.hom)
    (hS : ∀ i, Smooth ((M.components a).S i).hom)
    (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
    (hgenerate : ∀ i, ∃ n : ℕ, 0 < n ∧
      ∀ t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base,
        Function.Surjective ((M.components a).sumOfDifferences i n t))
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Z : Intrinsic.Detection.CM.ordinaryPoints R a → Intrinsic.Detection.CM.ordinaryPoints R a)
    (Y : Intrinsic.Detection.CM.ordinaryPoints R a → Multiset (Intrinsic.Detection.CM.ordinaryPoints R a))
    (h : Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y (fun i => act (H i))) :
    Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H :=
  polynomial_from_actual_ordinary_formulas R a
    hs hS hA hgenerate ho hd H Z Y h

theorem polynomial_of_algebra_formulas
    (hs : Smooth (M.integral a).toOver.hom)
    (hS : ∀ i, Smooth ((M.components a).S i).hom)
    (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
    (hgenerate : ∀ i, ∃ n : ℕ, 0 < n ∧
      ∀ t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base,
        Function.Surjective ((M.components a).sumOfDifferences i n t))
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Intrinsic.Frobenius.CM.specialAlbanese R a).X)
    (Z : Intrinsic.Detection.CM.ordinaryPoints R a → Intrinsic.Detection.CM.ordinaryPoints R a)
    (Y : Intrinsic.Detection.CM.ordinaryPoints R a → Multiset (Intrinsic.Detection.CM.ordinaryPoints R a))
    (h : AlgebraFormulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (fun f => ⇑(act f))
      (PointFrobenius.CM.ordinaryFrobenius R a hs) Z Y H) :
    Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (Intrinsic.Frobenius.CM.specialAlbanese R a).X) H :=
  polynomial_from_actual_ordinary_formulas R a
    hs hS hA hgenerate ho hd H Z Y h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData

end

end OAI
