import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone

/-! # Frame Diagonal Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap

noncomputable section

/-! The actual frame de Rham complexes map naturally into the native
diagonal section complex through the original global-to-open section maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp

local instance constPreservesZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def source : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  (FrameFunctor.functor p k n X Y f hp).op ⋙
    GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w n

def openTransformation : source p k n X Y f hp ⋙
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).mapHomologicalComplex (.up ℕ) ⟶
      P ⋙ (S).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (FrameFunctor.functor p k n X Y f hp).op
      (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w n))
    (((Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} Rcoeff)).obj
      (SectionBifunctor.specialOpens p k n X Y f).op).mapHomologicalComplex (.up ℕ))

def transformation : source p k n X Y f hp ⟶
    GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor (SectionBifunctor.rows p k n X Y f hp) :=
  GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation (source p k n X Y f hp)
    (P ⋙ (S).mapHomologicalComplex (.up ℕ)) (openTransformation p k n X Y f hp)

def map : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (source p k n X Y f hp) ⟶
    GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source X.left.affineOpens S P :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation p k n X Y f hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap
