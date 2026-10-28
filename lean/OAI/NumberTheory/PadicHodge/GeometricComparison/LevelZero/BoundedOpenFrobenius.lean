import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.InjectivePullbackCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

/-! # Bounded Open Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius

noncomputable section

/-! Actual level-zero crystalline Frobenius acts on the original
injective open-section complex and its flasque-sheaf presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport g hg 0

def flasqueTransformation : H ⟶ T ⋙ H where
  app I := ObjectProperty.homMk ((FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y).app I)
  naturality I J a := by
    apply ObjectProperty.hom_ext
    exact (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y).naturality a

variable (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

def resolutionMap : ((T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ I.cocomplex :=
  ExactInjective.ExactInjectivePullback.map T e I I

theorem resolutionMap_eq : resolutionMap p Y I = IntegralComparison.BoundedGeneral.ResolutionMap.map g hg 0 I I :=
  Bounded.InjectivePullbackCoordinates.BoundedInjectivePullbackCoordinates.map_eq g hg 0 I I

def map : IntegralComparison.BoundedOpen.SectionComplex.complex w 0 I ⟶ IntegralComparison.BoundedOpen.SectionComplex.complex w 0 I :=
  Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y) (resolutionMap p Y I)

def flasqueMap : IntegralComparison.BoundedOpen.FlasqueComplex.complex w 0 I ⟶ IntegralComparison.BoundedOpen.FlasqueComplex.complex w 0 I :=
  Section.CochainPullback.SectionCochainPullback.map T H H (flasqueTransformation p Y) (resolutionMap p Y I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius
