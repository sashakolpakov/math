import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ProductPreservation

/-! # Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Products

noncomputable section

/-!
# IntegralComparison: actual bounded crystalline products are preserved by inclusions between Witt levels
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm

instance inclusion_full : (F).Full := by
  dsimp [BoundedCrystalline.LevelMaps.inclusion]
  infer_instance

instance inclusion_faithful : (F).Faithful := by
  dsimp [BoundedCrystalline.LevelMaps.inclusion]
  infer_instance

def productIsLimit {U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
    (c : BinaryFan U V) (hc : IsLimit c) : IsLimit (c.map F) :=
  Incoming.ProductPreservation.isLimit F (BoundedCrystalline.LevelMaps.incomingLifts f n m hnm) c hc

def productMapConeIsLimit {U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
    (c : BinaryFan U V) (hc : IsLimit c) : IsLimit ((F).mapCone c) :=
  Incoming.ProductPreservation.isLimitMapCone F (BoundedCrystalline.LevelMaps.incomingLifts f n m hnm) c hc

instance preservesBinaryProduct (U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
    [HasBinaryProduct U V] : PreservesLimit (pair U V) F :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit (pair U V))
    (productMapConeIsLimit f n m hnm (limit.cone (pair U V)) (limit.isLimit (pair U V)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Products
