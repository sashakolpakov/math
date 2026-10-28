import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexF
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates

/-! # Frame Diagonal Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalCoordinates

noncomputable section

/-! The native frame-diagonal map has exactly the original frame-section
and Zariski restriction components. -/

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

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

variable (I : X.left.affineOpens)
local notation "FY" => CategoryTheory.Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X Y f hp) I

local instance constPreservesZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

omit [X.left.IsSeparated] in
theorem app_f (degree : ℕ) :
    ((FrameDiagonalMap.transformation p k n X Y f hp).app (op I)).f degree =
      (ConstantSection.ComplexRestriction.sectionMap.{1, 0, 2} Rcoeff
        (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
        (BoundedFrame.DeRhamSections.frameComplex w n FY)
        (Bounded.RelativeSheafComplex.complex w n FY)
        (BoundedFrame.DeRhamSections.sheafMap w n FY)).f degree ≫
      ((GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w n).app
        ((Bounded.RelativeSheafComplex.complex w n FY).X degree)).app (op (f ⁻¹ᵁ I.val)) := by
  have h₁ := GeometricComparison.ConstantComplexF.ConstantComplexDiagonalCoordinates.app_f
    (FrameDiagonalMap.source p k n X Y f hp)
    (P ⋙ (S).mapHomologicalComplex (.up ℕ))
    (FrameDiagonalMap.openTransformation p k n X Y f hp) (op I) degree
  have h₂ := GeometricComparison.Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates.open_app_f w n (op FY) (op (f ⁻¹ᵁ I.val)) degree
  have h₃ := GeometricComparison.Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app_f w n (op FY) degree
  exact h₁.trans (h₂.trans (congrArg (fun a => a ≫
    ((GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w n).app
      ((Bounded.RelativeSheafComplex.complex w n FY).X degree)).app (op (f ⁻¹ᵁ I.val))) h₃))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalCoordinates
