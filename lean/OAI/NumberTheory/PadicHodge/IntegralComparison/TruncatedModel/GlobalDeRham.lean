import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryBaseIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryCechCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

/-! # Global De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham.Comparison

noncomputable section

/-! The ordinary de Rham Čech total of an actual smooth proper model
over a finite Witt level computes the original bounded crystalline
cohomology of its actual special fiber in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens S X)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex.Comparison.pdComplexes p k n X Y f hp
local notation "U" => ModuleCat.restrictScalars (algebraMap W S)

abbrev coefficientFunctor : ModuleCat.{0} W ⥤ ModuleCat.{2} R :=
  SmoothWitt.DeRham.Comparison.coefficientFunctor p k

instance coefficientFunctor_additive : (coefficientFunctor p k).Additive := by
  dsimp only [coefficientFunctor]
  infer_instance

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham.Comparison.coefficientFunctor p k

def frameDiagramIso : P ⋙ (F).mapHomologicalComplex (.up ℕ) ≅
    FrameDiagonalMap.source p k n X Y f hp := Iso.refl _

def frameIso : ((F).mapHomologicalComplex (.up ℕ)).obj (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N P) ≅
    GlobalFrame.Comparison.complex p k n X Y f hp :=
  GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F N (Small.OrdinaryCechTotal.Ordinary.finiteIndices S X) P

def rawComplex : CochainComplex (ModuleCat.{0} W) ℕ :=
  ((U).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total S X)

def ordinaryIso : rawComplex p k n X ≅ GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total N P :=
  OrdinaryCechCoordinates.Ordinary.iso p k n X ≪≫
    GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso N (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).symm

def complex : CochainComplex (ModuleCat.{2} R) ℕ :=
  ((F).mapHomologicalComplex (.up ℕ)).obj (rawComplex p k n X)

def iso : complex p k n X ≅ GlobalFrame.Comparison.complex p k n X Y f hp :=
  ((F).mapHomologicalComplex (.up ℕ)).mapIso (ordinaryIso p k n X Y f hp) ≪≫
    frameIso p k n X Y f hp

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def homologyIso (i : ℕ) : (complex p k n X).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y) n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (iso p k n X Y f hp) ≪≫
    GlobalFrame.Comparison.homologyIso p k n X Y f hp J i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalDeRham.Comparison
