import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittProductFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyProductProperty
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.TupleProducts

/-! # Witt Tuple Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleFlatness

noncomputable section

/-! Every actual Čech tuple product of the constructed Witt frames is flat over its original truncated coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev Objects := BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n

def FlatObject (U : Objects p k X n) : Prop :=
  (BoundedCrystalline.BaseRing.base (Witt.Crystalline.wittStructureMap p k X) n U).Flat

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] in
theorem iso_flat {U V : Objects p k X n} (e : U ≅ V) (hU : FlatObject p k X n U) : FlatObject p k X n V := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  exact BoundedCrystalline.BaseRing.flat_of_hom (Witt.Crystalline.wittStructureMap p k X) n e.inv
    (Crystalline.ProductFlatnessTransport.iso (L.mapIso e.symm)) hU

theorem binary_flat (U : Objects p k X n) (hU : FlatObject p k X n U) (i : StandardCover.Index k X) :
    FlatObject p k X n (U ⨯ WittFrameFamily.Family.frame p k X n i) :=
  BoundedCrystalline.BaseRing.flat_of_hom (Witt.Crystalline.wittStructureMap p k X) n prod.fst
    (WittProductFlatness.bounded_projection p k X n i U
      (BinaryFan.mk prod.fst prod.snd) (prodIsProd U (WittFrameFamily.Family.frame p k X n i))) hU

theorem tuple_flat (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    FlatObject p k X n (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t) :=
  NonemptyProductProperty.product (WittFrameFamily.Family.frame p k X n) (FlatObject p k X n)
    (fun e hU => iso_flat p k X n e hU) (WittProductFlatness.frame_flat p k X n)
    (binary_flat p k X n) a t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleFlatness
