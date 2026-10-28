import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeLifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ProductPreservation

/-! # Postcompose Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeProducts

noncomputable section

/-!
# IntegralComparison: actual bounded crystalline products are preserved by geometric monomorphisms
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

def productIsLimit {U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
    (c : BinaryFan U V) (hc : IsLimit c) : IsLimit (c.map F) :=
  Incoming.ProductPreservation.isLimit F (PostcomposeLifts.incomingLifts g hg n) c hc

def productMapConeIsLimit {U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
    (c : BinaryFan U V) (hc : IsLimit c) : IsLimit ((F).mapCone c) :=
  Incoming.ProductPreservation.isLimitMapCone F (PostcomposeLifts.incomingLifts g hg n) c hc

instance preservesBinaryProduct (U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
    [HasBinaryProduct U V] : PreservesLimit (pair U V) F :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit (pair U V))
    (productMapConeIsLimit g hg n (limit.cone (pair U V)) (limit.isLimit (pair U V)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeProducts
