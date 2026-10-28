import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexF
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates

/-! # Frame Diagonal Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalCoordinates.IntrinsicPadicFrameDiagonalCoordinates

noncomputable section

/-! The native frame-diagonal map has exactly the original frame-section
and Zariski restriction components. -/

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

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

variable (I : X.left.affineOpens)
local notation "FY" => CategoryTheory.Functor.obj (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n) I

local instance constPreservesZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

omit [X.left.IsSeparated] in
theorem app_f (k : ℕ) :
    ((FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.transformation p X Y f hp n).app (op I)).f k =
      (IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{1, 0, 2} Rcoeff
        (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n)
        (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex w n FY)
        (IntegralComparison.Bounded.RelativeSheafComplex.complex w n FY)
        (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap w n FY)).f k ≫
      ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w n).app
        ((IntegralComparison.Bounded.RelativeSheafComplex.complex w n FY).X k)).app (op (f ⁻¹ᵁ I.val)) := by
  have h₁ := ConstantComplexF.ConstantComplexDiagonalCoordinates.app_f
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n)
    (P ⋙ (S).mapHomologicalComplex (.up ℕ))
    (FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n) (op I) k
  have h₂ := Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates.open_app_f w n (op FY) (op (f ⁻¹ᵁ I.val)) k
  have h₃ := Frame.OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app_f w n (op FY) k
  exact h₁.trans (h₂.trans (congrArg (fun a => a ≫
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w n).app
      ((IntegralComparison.Bounded.RelativeSheafComplex.complex w n FY).X k)).app (op (f ⁻¹ᵁ I.val))) h₃))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonalCoordinates.IntrinsicPadicFrameDiagonalCoordinates
