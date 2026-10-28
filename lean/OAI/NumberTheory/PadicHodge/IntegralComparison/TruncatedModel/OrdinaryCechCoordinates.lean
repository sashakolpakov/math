import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal

/-! # Ordinary Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryCechCoordinates.Ordinary

noncomputable section

/-! The small native de Rham total in ordinary affine-ring
coordinates, before passing to PD frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "W" => WittVector p k
local notation "U" => ModuleCat.restrictScalars (algebraMap W R)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X)

def iso :
    ((U).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total R X) ≅
      GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N (OrdinaryBaseIso.Ordinary.target p k n X) :=
  ((U).mapHomologicalComplex (.up ℕ)).mapIso (Small.OrdinaryCechTotal.Ordinary.totalIso R X).symm ≪≫
    GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso U N (Small.OrdinaryCechTotal.Ordinary.finiteIndices R X)
      (Small.OrdinaryCechTotal.Ordinary.diagram R X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryCechCoordinates.Ordinary
