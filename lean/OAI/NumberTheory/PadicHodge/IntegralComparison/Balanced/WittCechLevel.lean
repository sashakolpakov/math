import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittLevelResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyTransport

/-! # Witt Cech Level -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCechLevel

noncomputable section

/-! The native Witt ring Čech transition computes the original crystalline
level transition through the augmentation-normalized comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem comparison (n i : ℕ) :
    HomologicalComplex.homologyMap (SmoothProper.WittCechResolution.Comparison.iso p k X n).inv i ≫
      (SmoothProperWittCup.resolutionHomologyIso p k X n i).hom =
        (SmoothProperWittCup.homologyIso p k X n i).hom := by
  let a := BoundedFrame.CechPresheafCohomology.sheafIso p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
  let b := BoundedFrame.CechCohomology.comparison p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
  let d := (SmoothProperWittCup.resolutionHomologyIso p k X n i).hom
  exact (congrArg (fun c => c ≫ d) (HomologicalComplex.homologyMap_comp a.hom b.inv i)).trans
    (Category.assoc _ _ _)

variable (n m : ℕ) (hnm : n ≤ m)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (SmoothProper.WittCechNaturality.Comparison.liftedMap p k X n m hnm) i ≫
      (SmoothProperWittCup.homologyIso p k X n i).hom =
        (SmoothProperWittCup.homologyIso p k X m i).hom ≫
          ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) := by
  let a := HomologicalComplex.homologyMap
    (SmoothProper.WittCechNaturality.Comparison.liftedMap p k X n m hnm) i
  let d := (SmoothProperWittCup.resolutionHomologyIso p k X n i).hom
  let c := HomologicalComplex.homologyMap (SmoothProper.WittCechResolution.Comparison.iso p k X m).inv i
  let g := ModuleCat.ofHom (Bounded.CohomologyTransition.map (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm i)
  have hs := InverseCoordinateHomology.homology
    (SmoothProper.WittCechResolution.Comparison.iso p k X m)
    (SmoothProper.WittCechResolution.Comparison.iso p k X n)
    (SmoothProper.WittResolutionLevelCohomology.map p k X n m hnm)
    (SmoothProper.WittCechNaturality.Comparison.liftedMap p k X n m hnm)
    (SmoothProper.WittCechNaturality.Comparison.complexes p k X n m hnm) i
  exact (congrArg (fun b => a ≫ b) (comparison p k X n i).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ d) hs).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun b => c ≫ b) (WittLevelResolution.homology p k X n m hnm i)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun b => b ≫ g) (comparison p k X m i)))))))

local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.map (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm

theorem transport (i : ℕ) (x : (SmoothProper.WittCechTransitionData.complex p k X m).homology i) :
    ((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (SmoothProper.WittCechTransitionData.complex p k X n) i).trans
        (SmoothProperWittCup.homologyIso p k X n i).toLinearEquiv)
          (HomologicalComplex.homologyMap (SmoothProper.WittCechTransition.map p k X n m hnm) i x) =
      g i (((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
        (SmoothProper.WittCechTransitionData.complex p k X m) i).trans
          (SmoothProperWittCup.homologyIso p k X m i).toLinearEquiv) x) :=
  Lifted.HomologyTransport.naturality.{u + 1, u + 1, u + 2} R
    (SmoothProper.WittCechTransition.map p k X n m hnm) i
    (SmoothProperWittCup.homologyIso p k X m i)
    (SmoothProperWittCup.homologyIso p k X n i) (ModuleCat.ofHom (g i))
    (WittCechLevel.homology p k X n m hnm i) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCechLevel
