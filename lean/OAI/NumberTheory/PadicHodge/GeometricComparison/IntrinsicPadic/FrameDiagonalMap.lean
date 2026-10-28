import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone

/-! # Frame Diagonal Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap

noncomputable section

/-! The actual frame de Rham complexes map naturally into the native
diagonal section complex through the original global-to-open section maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n

local instance constPreservesZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def source : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op ⋙
    Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w n

def openTransformation : source p X Y f hp n ⋙
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).mapHomologicalComplex (.up ℕ) ⟶
      P ⋙ (S).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op
      (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w n))
    (((Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op).mapHomologicalComplex (.up ℕ))

def transformation : source p X Y f hp n ⟶
    BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.IntrinsicPadicSectionBifunctor.rows p X Y f hp n) :=
  ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation (source p X Y f hp n)
    (P ⋙ (S).mapHomologicalComplex (.up ℕ)) (openTransformation p X Y f hp n)

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (source p X Y f hp n) ⟶
    Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S P :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap
