import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallinePDCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves

/-! # Principal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison

noncomputable section

/-! The local principal PD complex maps to the original injective
resolution on the same actual affine opens of a smooth finite-level model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U

def nativeDiagram : Cᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  (F ⋙ FrameFunctor.functor p k n X Y f hp).op ⋙
    GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded w n

def nativePDMap : Supported.PDComplex.localizedComplex p k Y Q ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (nativeDiagram p k n X Y f hp U) :=
  PrincipalFrame.pdMap p k n X Y f hp U ≫
    ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).mapIso (Functor.isoWhiskerLeft (Functor.op F)
      (Open.CrystallinePDCoordinates.iso p k Y
        (SmallFrame.bigFunctor p k n X Y f hp)
        (SmallFrame.mapToX_open p k n X Y f hp)))).hom

def coefficients : ModuleCat W ⥤ ModuleCat.{2} R :=
  Crystalline.RelativeResolution.coefficientFunctor (B := W) ⋙ ModuleCat.uliftFunctor.{2, 1} R

instance coefficients_additive : (coefficients p k).Additive := by
  dsimp only [coefficients]
  infer_instance

def source : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) (coefficients p k)).mapHomologicalComplex
    (.up ℕ)).obj (Supported.PDComplex.localizedComplex p k Y Q)

def coefficientMap : source p k n X Y f hp U ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (Functor.op F ⋙ FrameDiagonalMap.source p k n X Y f hp) :=
  ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves (T := Cᵒᵖ) (coefficients p k)).mapHomologicalComplex
    (.up ℕ)).map (nativePDMap p k n X Y f hp U) ≫
      (GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso (coefficients p k) (nativeDiagram p k n X Y f hp U)).inv

def restriction : (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Cᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (Functor.op F)

instance restriction_additive : (restriction p k n X U).Additive where
  map_add := rfl

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : source p k n X Y f hp U ⟶
    ((restriction p k n X U).mapHomologicalComplex (.up ℕ)).obj
      (((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :=
  coefficientMap p k n X Y f hp U ≫
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (Functor.op F) (𝟭 (ModuleCat.{2} R)) (.up ℕ)
      (FrameDiagonalMap.source p k n X Y f hp)).inv ≫
    ((restriction p k n X U).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.Comparison.map p k n X Y f hp I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison
