import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IsoConjugation

/-! # Quotient Frame Natural Iso -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientFrameNaturalIso

/-! The canonical quotient algebra diagram is naturally the original native frame algebra diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "quotients" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n
local notation "rings" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp n

theorem conjugation {I J : X.left.affineOpens} (α : I ⟶ J) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom ≫ (rings).map α.op ≫
      (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv = (quotients).map α.op :=
  QuotientFrameNaturality.IntrinsicPadicQuotientFrameNaturality.conjugatedMap_eq p X Y f hp n α

theorem natural {I J : X.left.affineOpens} (α : I ⟶ J) :
    (quotients).map α.op ≫ (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).hom =
      (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom ≫ (rings).map α.op :=
  IsoConjugation.IsoConjugationSquare.square
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J)
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I)
    ((quotients).map α.op) ((rings).map α.op) (conjugation p X Y f hp n α)

def iso : quotients ≅ rings :=
  NatIso.ofComponents (fun I => AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I.unop)
    (fun {_ _} α => natural p X Y f hp n α.unop)

def reduction : IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X ⟶ rings :=
  AlgebraQuotient.IntrinsicPadicAlgebraQuotient.reduction p X n ≫ (iso p X Y f hp n).hom

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientFrameNaturalIso

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap

/-! Original integral affine rings reduce naturally to the actual native
frame rings, whose structural action kills the coefficient prime-power ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp n

def transformation : A ⟶ B :=
  IntrinsicPadicQuotientFrameNaturalIso.reduction p X Y f hp n

private theorem power_annihilation {R S : Type*} [CommRing R] [CommRing S]
    (q m : ℕ) (φ : R →+* S) (h : (q : S) ^ (m + 1) = 0) :
    ∀ r, r ∈ (Ideal.span {(q : R)}) ^ (m + 1) → φ r = 0 := by
  have hi : (Ideal.span {(q : R)}) ^ (m + 1) ≤ RingHom.ker φ := by
    rw [Ideal.span_singleton_pow, Ideal.span_le]
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    change φ ((q : R) ^ (m + 1)) = 0
    rw [map_pow, map_natCast, h]
  exact fun _ hr => hi hr

theorem annihilation (I : X.left.affineOpensᵒᵖ) (r : W)
    (hr : r ∈ (Ideal.span {(p : W)}) ^ (n + 1)) : algebraMap W ((B).obj I) r = 0 :=
  power_annihilation p n (algebraMap W ((B).obj I))
    (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.unop.val I.unop.property n).property r hr

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap

end

end OAI
