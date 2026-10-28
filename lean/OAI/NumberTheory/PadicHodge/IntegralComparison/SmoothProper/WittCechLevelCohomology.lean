import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Witt Cech Level Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLevelCohomology

noncomputable section

/-! The actual global Witt ring Čech transition induces exactly the original bounded crystalline Ext transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (WittCechNaturality.Comparison.liftedMap p k X n m hnm) i ≫
      (WittCechCohomology.homologyIso p k X n i).hom =
        (WittCechCohomology.homologyIso p k X m i).hom ≫
          ModuleCat.ofHom (Bounded.CohomologyTransition.map (Witt.Crystalline.wittStructureMap p k X) n m hnm i) := by
  let a := HomologicalComplex.homologyMap (WittCechNaturality.Comparison.liftedMap p k X n m hnm) i
  let d := (WittFrameCohomology.homologyIso p k X n i).hom
  let c := HomologicalComplex.homologyMap (WittCechResolution.Comparison.iso p k X m).inv i
  let g := ModuleCat.ofHom (Bounded.CohomologyTransition.map (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm i)
  have hs := InverseCoordinateHomology.homology
    (WittCechResolution.Comparison.iso p k X m)
    (WittCechResolution.Comparison.iso p k X n)
    (WittResolutionLevelCohomology.map p k X n m hnm)
    (WittCechNaturality.Comparison.liftedMap p k X n m hnm)
    (WittCechNaturality.Comparison.complexes p k X n m hnm) i
  exact (congrArg (fun b => a ≫ b) (WittCechResolution.Comparison.homology p k X n i).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ d) hs).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun b => c ≫ b) (WittResolutionLevelCohomology.homology p k X n m hnm i)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun b => b ≫ g) (WittCechResolution.Comparison.homology p k X m i)))))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechLevelCohomology
