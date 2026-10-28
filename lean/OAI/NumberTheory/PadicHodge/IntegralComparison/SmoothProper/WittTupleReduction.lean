import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ReductionIsoKernel

/-! # Witt Tuple Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction

noncomputable section

/-! Every actual Witt frame Čech tuple has the canonical prime-power quotient transition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def reduction : WittTupleFlatness.Objects p k X m ⥤
    WittTupleFlatness.Objects p k X n :=
  BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) m ⋙
    Crystalline.LevelReductionFunctor.functor n

instance preservesTuples (a : ℕ) : PreservesLimitsOfShape (Discrete (Fin (a + 1))) (reduction p k X n m) := by
  dsimp only [reduction]
  infer_instance

variable (hnm : n ≤ m) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)

def iso : Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t ≅
    (reduction p k X n m).obj (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t) :=
  Pi.mapIso (fun b => WittFrameReduction.iso p k X n m hnm (t b)) ≪≫
    (PreservesProduct.iso (reduction p k X n m) (fun b => WittFrameFamily.Family.frame p k X m (t b))).symm

def bigIso : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t).obj ≅
    Crystalline.LevelReduction.object n (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t).obj :=
  (BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) n).mapIso (WittTupleReduction.iso p k X n m hnm a t)

def morphism : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t).obj ⟶
    (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t).obj :=
  Crystalline.ReductionIsoKernel.morphism n (bigIso p k X n m hnm a t)

theorem surjective : Function.Surjective (morphism p k X n m hnm a t).ringMap :=
  Crystalline.ReductionIsoKernel.surjective n (bigIso p k X n m hnm a t)

theorem kernel : RingHom.ker (morphism p k X n m hnm a t).ringMap.toRingHom =
    (Ideal.span {(p : (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t).obj.ring)}) ^ (n + 1) :=
  Crystalline.ReductionIsoKernel.kernel n (bigIso p k X n m hnm a t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction
