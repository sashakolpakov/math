import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap

/-! # Frame Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic

noncomputable section

/-! Canonical Ext-zero sections of the original native frame cone have
the same source coordinates as its literal constant-sheaf Čech map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

private theorem replace_left {C : Type*} [Category C] {A B D : C}
    (a a' : A ⟶ B) (t : B ⟶ D) (b : A ⟶ D)
    (ha : a = a') (h : a' ≫ t = b) : a ≫ t = b :=
  (congrArg (fun q => q ≫ t) ha).trans h

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := W)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSourceCoordinates.Intrinsic.constantFunctor p Y n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.complex p X Y f hp n
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.map p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts CR JT

abbrev coefficientSource := Crystalline.ConeProduct.coefficientSource W M
abbrev coefficientComplex := Crystalline.SheafComplexProduct.coefficientComplex W K
abbrev coefficientMap := Crystalline.ConeProduct.coefficientMap W M K a

abbrev sourceTotal := GeometricComparison.CechCone.Total.CechConeTotal.total U
  (Q ⋙ (F).mapHomologicalComplex (.up ℕ))
abbrev targetTotal := GeometricComparison.CechCone.Total.CechConeTotal.total U P
abbrev levelMap := GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map T U
  (Q ⋙ (F).mapHomologicalComplex (.up ℕ)) P
  (FrameSourceCoordinates.Intrinsic.transformation p X Y f hp n)

abbrev sheaf_square := replace_left _ _ _ _
  (Crystalline.SheafConstantCoordinates.map_eq W JT M K a)
  (FrameSourceCoordinates.Intrinsic.comparison p X Y f hp n)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

abbrev sectionsMap_eq := Balanced.SheafifiedSourceCoordinates.sectionsMap_eq.{1,2}
  CR JT I (coefficientSource p X Y f hp n) (coefficientComplex p X Y f hp n)
  (coefficientMap p X Y f hp n) (GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I)
  (sourceTotal p X Y f hp n) (targetTotal p X Y f hp n)
  (FrameSourceCoordinates.Intrinsic.sourceIso p X Y f hp n)
  (GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n)
  (levelMap p X Y f hp n) (sheaf_square p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic
