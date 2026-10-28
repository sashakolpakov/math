import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Presheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

/-! # Witt Cech Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechResolution.Comparison

noncomputable section

/-! The original global source-resolution cochains identify explicitly with the native Witt ring Čech cochains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Site" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
local notation "CoeffSheaf" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def coefficientIso : WittCechTransitionData.sections p k X n ≅ (CoeffSheaf).obj :=
  Functor.isoWhiskerLeft (BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) n).op
    (Crystalline.StructureDescent.structurePresheafIso (Witt.Crystalline.wittStructureMap p k X))

def iso : WittFrameCohomology.complex p k X n ≅ WittCechCohomology.complex p k X n :=
  FrameCech.Presheaf.Comparison.comparison.{u + 1, u, u + 2} (WittFrameFamily.Family.frame p k X n) R Site CoeffSheaf
    (WittCechTransitionData.sections p k X n) (coefficientIso p k X n)

theorem coordinate_mk (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (f : (WittPresentationResolution.complex p k X n).X a ⟶ CoeffSheaf) :
    WittCechTransitionData.coordinate p k X n a t
      (((iso p k X n).hom.f a (Abelian.Ext.mk₀ f)).down) =
        (coefficientIso p k X n).inv.app (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))
          (Presentation.ResolutionCoordinates.sheaf.{u + 1, u} (WittFrameFamily.Family.frame p k X n) R a Site CoeffSheaf f t) :=
  FrameCech.Presheaf.Comparison.coordinate_mk.{u + 1, u, u + 2} (WittFrameFamily.Family.frame p k X n) R Site CoeffSheaf
    (WittCechTransitionData.sections p k X n) (coefficientIso p k X n) a t f

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (iso p k X n).inv i ≫
    (WittFrameCohomology.homologyIso p k X n i).hom =
      (WittCechCohomology.homologyIso p k X n i).hom := by
  let a := BoundedFrame.CechPresheafCohomology.sheafIso p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n)
  let b := BoundedFrame.CechCohomology.comparison p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n)
  let d := (WittFrameCohomology.homologyIso p k X n i).hom
  exact (congrArg (fun c => c ≫ d) (HomologicalComplex.homologyMap_comp a.hom b.inv i)).trans (Category.assoc _ _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechResolution.Comparison
