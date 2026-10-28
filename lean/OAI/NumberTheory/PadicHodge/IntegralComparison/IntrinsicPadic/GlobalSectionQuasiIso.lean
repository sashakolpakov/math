import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ConstantOpenCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalAugmentationQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechInjectiveQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.OpenCechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.GlobalResolutionQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CechMapQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexPostcompose
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation

/-! # Global Section Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalSectionQuasiIso.IntrinsicFrame

noncomputable section

/-! The actual frame source computes original injective crystalline
sections in every degree. The proof uses the certified open Čech cone,
its actual map into injectives, and the genuine flasque injective edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.sourceTotal p X Y f hp n
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.targetTotal p X Y f hp n
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSectionCoordinates.Intrinsic.levelMap p X Y f hp n
local notation "t" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf
      (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts CR JT

local instance tuple_preserves (m : ℕ)
    (b : Fin (m+1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (U ∘ b)) F :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.composite_preserves X.left Y.left f (U ∘ b)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n ⋙
  Functor.mapHomologicalComplex (Crystalline.RelativeResolution.coefficientFunctor (B := W))
    (ComplexShape.up ℕ)
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n

local instance constZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} CR ⥤
      X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} CR).PreservesZeroMorphisms where
  map_zero _ _ := rfl

theorem quasiIso : QuasiIso (ConstantSection.ComplexMap.map.{1,0,1,2} CR JT M
    I.cocomplex (a ≫ (t).inv ≫ GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I)) := Constant.GlobalResolutionQuasiIso.quasiIso_of_evaluation.{1,0,1,2,0}
  CR JT G S
  (ConstantOpenCoordinates.Intrinsic.extIso p Y n)
  (ConstantOpenCoordinates.Intrinsic.restriction p X Y f n) U Q P
  (FrameSourceCoordinates.Intrinsic.transformation p X Y f hp n)
  (GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n)
  (ConstantOpenCoordinates.Intrinsic.transformation_eq p X Y f hp n)
  (GlobalAugmentationQuasiIso.Intrinsic.quasiIso p X Y f hp n)
  t (GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I)
  (Bounded.OpenCechQuasiIso.Global.quasiIso
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n I F U
    (GeometricComparison.IntrinsicPadic.InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f))
  (CechInjectiveQuasiIso.IntrinsicOpen.evaluation_quasiIso p X Y f hp n I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.GlobalSectionQuasiIso.IntrinsicFrame
