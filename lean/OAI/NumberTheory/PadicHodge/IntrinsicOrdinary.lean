import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial

/-! # Intrinsic Ordinary -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary

noncomputable section

/-! Full CubicRelation input, instantiated at the geometric special-fiber endomorphisms.
The source ordinary-point hypotheses are retained verbatim. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

/-- Full unchanged CubicRelation proposition; no statement proof is imported. -/
def CubicRelationInput : Prop := ∀
    (q : ℕ) (_hq : q.Prime)
    {R A O J : Type*}
    [Ring R] [AddCommGroup A]
    (act : R →+* AddMonoid.End A)
    (component : O → J)
    (a : O → A)
    (Φ C0 T1 T2 T3 : R)
    (X Z : O → O)
    (Y : O → Multiset O)
    (_hXcomponent : ∀ x, component (X x) = component x)
    (_hFrobenius : ∀ x, act Φ (a x) = a (X x))
    (_hXY : ∀ x, (Y x).map X = Y (X x))
    (_hXZ : ∀ x, X (Z x) = Z (X x))
    (_hT1 : ∀ x y, component x = component y →
      act (C0 * T1) (a x - a y) =
        a (X x) - a (X y) +
          q • (((Y x).map a).sum - ((Y y).map a).sum))
    (_hT2 : ∀ x y, component x = component y →
      act (C0 ^ 2 * T2) (a x - a y) =
        ((Y (X x)).map a).sum - ((Y (X y)).map a).sum +
          q ^ 2 • (a (Z x) - a (Z y)))
    (_hT3 : ∀ x y, component x = component y →
      act (C0 ^ 3 * T3) (a x - a y) =
        a (Z (X x)) - a (Z (X y)))
    (_hdetect : ∀ f : R,
      (∀ x y, component x = component y →
        act f (a x - a y) = 0) → f = 0),
    Φ ^ 3 - C0 * T1 * Φ ^ 2 +
      q • (C0 ^ 2 * T2 * Φ) -
      q ^ 3 • (C0 ^ 3 * T3) = 0

/-- Exactly the natural point-action premises in CubicRelation, for fixed operators. -/
structure OrdinaryData {R : Type*} [Ring R] (q : ℕ) (Φ C t₁ t₂ t₃ : R) where
  Points : Type
  [pointGroup : AddCommGroup Points]
  Ordinary : Type
  Components : Type
  act : R →+* AddMonoid.End Points
  component : Ordinary → Components
  a : Ordinary → Points
  X : Ordinary → Ordinary
  Z : Ordinary → Ordinary
  Y : Ordinary → Multiset Ordinary
  hXcomponent : ∀ x, component (X x) = component x
  hFrobenius : ∀ x, act Φ (a x) = a (X x)
  hXY : ∀ x, (Y x).map X = Y (X x)
  hXZ : ∀ x, X (Z x) = Z (X x)
  hT1 : ∀ x y, component x = component y →
    act (C * t₁) (a x - a y) = a (X x) - a (X y) +
      q • (((Y x).map a).sum - ((Y y).map a).sum)
  hT2 : ∀ x y, component x = component y →
    act (C ^ 2 * t₂) (a x - a y) =
      ((Y (X x)).map a).sum - ((Y (X y)).map a).sum +
        q ^ 2 • (a (Z x) - a (Z y))
  hT3 : ∀ x y, component x = component y →
    act (C ^ 3 * t₃) (a x - a y) = a (Z (X x)) - a (Z (X y))
  hdetect : ∀ f : R,
    (∀ x y, component x = component y → act f (a x - a y) = 0) → f = 0

attribute [instance] OrdinaryData.pointGroup

theorem specialized_polynomial_from_full_CubicRelation
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
    {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (C t₁ t₂ t₃ : H)
    (hCubicRelation : CubicRelationInput.{0, 0, 0, 0})
    (O : OrdinaryData q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ C)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ t₁)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ t₂)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ t₃)) :
    AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ
        ((![C * t₁, C ^ 2 * t₂, C ^ 3 * t₃] : Fin 3 → H) i)) = 0 := by
  have h := hCubicRelation q (Fact.out : q.Prime) O.act O.component O.a _ _ _ _ _
    O.X O.Z O.Y O.hXcomponent O.hFrobenius O.hXY O.hXZ
    O.hT1 O.hT2 O.hT3 O.hdetect
  simpa [AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue] using h

end

end OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
