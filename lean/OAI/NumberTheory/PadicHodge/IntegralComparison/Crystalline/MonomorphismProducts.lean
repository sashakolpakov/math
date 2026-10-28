import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Continuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ProductPreservation

/-! # Monomorphism Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.MonomorphismProducts

noncomputable section

/-!
# IntegralComparison: crystalline products survive monomorphisms of the underlying scheme

Postcomposition along a scheme monomorphism is fully faithful. The
already constructed incoming crystalline lifts then show that actual
binary products are preserved. This includes affine open embeddings and
isomorphisms used to place polynomial frames on the global scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f)

def preimage {U V : BigCrystallineSite.Object p B J δ f}
    (a : (BigCrystallineSite.postcompose g hg).obj U ⟶ (BigCrystallineSite.postcompose g hg).obj V) : U ⟶ V where
  ringMap := a.ringMap
  overBase := a.overBase
  overX := by
    apply (cancel_mono g).mp
    exact (Category.assoc _ _ _).trans a.overX

instance postcompose_full : (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).Full where
  map_surjective a := ⟨preimage g hg a, by apply BigCrystallineSite.Object.Hom.ext; rfl⟩

def productIsLimit {U V : BigCrystallineSite.Object p B J δ f} (c : BinaryFan U V) (hc : IsLimit c) :
    IsLimit (c.map (BigCrystallineSite.postcompose g hg)) :=
  Incoming.ProductPreservation.isLimit (BigCrystallineSite.postcompose g hg)
    (Continuous.incomingLifts g hg) c hc

def productMapConeIsLimit {U V : BigCrystallineSite.Object p B J δ f} (c : BinaryFan U V) (hc : IsLimit c) :
    IsLimit ((BigCrystallineSite.postcompose g hg).mapCone c) :=
  Incoming.ProductPreservation.isLimitMapCone (BigCrystallineSite.postcompose g hg)
    (Continuous.incomingLifts g hg) c hc

instance preservesBinaryProduct (U V : BigCrystallineSite.Object p B J δ f) [HasBinaryProduct U V] :
    PreservesLimit (pair U V) (BigCrystallineSite.postcompose g hg) :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit (pair U V))
    (productMapConeIsLimit g hg (limit.cone (pair U V)) (limit.isLimit (pair U V)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.MonomorphismProducts
