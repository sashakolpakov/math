import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrameIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexF

/-! # Principal In -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family

/-! The native principal charts are one family of original bounded
frames, with their actual restriction maps to the center chart. -/

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
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X Y f hp
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev frames := (F ⋙ G).op
abbrev opens := (F ⋙ SectionBifunctor.specialOpens p k n X Y f).op
abbrev center := op ((G).obj U)

def cone : (Functor.const Cᵒᵖ).obj (center p k n X Y f hp U) ⟶ frames p k n X Y f hp U where
  app r := ((G).map (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop)).op
  naturality r s a := by
    change 𝟙 _ ≫ ((G).map (AffinePrincipal.Diagram.projection X.left U.val U.property s.unop)).op =
      ((G).map (AffinePrincipal.Diagram.projection X.left U.val U.property r.unop)).op ≫
        ((G).map ((F).map a.unop)).op
    rw [Category.id_comp, ← op_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (fun a => ((G).map a).op)
      (AffinePrincipal.Diagram.projection_natural X.left U.val U.property a.unop).symm

omit [IsProper X.hom] [X.left.IsSeparated] in
theorem resolutionCone_eq :
    BoundedFrame.FamilySections.Family.cone w n (center p k n X Y f hp U) (cone p k n X Y f hp U) =
      PrincipalFrameSections.cone p k n X Y f hp U := by
  apply NatTrans.ext
  funext r
  rw [BoundedFrame.FamilySections.Family.cone_app]
  rfl

omit [IsProper X.hom] in
theorem fixed_isIso : IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map
    (BoundedFrame.FamilySections.Family.sections w n (opens p k n X Y f U))
    ((Q).obj (center p k n X Y f hp U))
    (BoundedFrame.FamilySections.Family.diagram w n (frames p k n X Y f hp U))
    (BoundedFrame.FamilySections.Family.cone w n (center p k n X Y f hp U) (cone p k n X Y f hp U))) := by
  rw [resolutionCone_eq]
  exact PrincipalFrameIso.fixed_isIso p k n X Y f hp U

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.DiagonalCoordinates

/-! The original native frame diagonal map, restricted to principal
opens, is the actual bounded-frame family diagonal map. -/

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X Y f hp U
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X Y f U
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X U
local notation "S₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.sections p k n X Y f
local notation "P₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def diagonal := GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal
  (BoundedFrame.FamilySections.Family.sections w n O)
  (BoundedFrame.FamilySections.Family.source w n G)
  (BoundedFrame.FamilySections.Family.diagram w n G)
  (BoundedFrame.FamilySections.Family.openTransformation w n O G)

/-- The family diagonal written in the original target frame. -/
def diagonalInTarget := diagonal p k n X Y f hp U ≫
  (PrincipalFrameSections.targetIso p k n X Y f hp U).hom

/-- The original frame diagonal transported to the principal-open family. -/
def transportedDiagonal :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (Functor.op F) (𝟭 (ModuleCat.{2} R)) (.up ℕ)
    (FrameDiagonalMap.source p k n X Y f hp)).inv ≫
  ((H).mapHomologicalComplex (.up ℕ)).map (FrameDiagonalMap.map p k n X Y f hp)

omit [IsProper X.hom] in
theorem coordinates : diagonalInTarget p k n X Y f hp U =
    transportedDiagonal p k n X Y f hp U := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  change ((GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation
      (BoundedFrame.FamilySections.Family.source w n G)
      ((BoundedFrame.FamilySections.Family.diagram w n G) ⋙
        (BoundedFrame.FamilySections.Family.sections w n O).mapHomologicalComplex (.up ℕ))
      (BoundedFrame.FamilySections.Family.openTransformation w n O G)).app r).f q ≫ 𝟙 _ =
    𝟙 _ ≫ ((FrameDiagonalMap.transformation p k n X Y f hp).app
      ((Functor.op F).obj r)).f q
  rw [Category.comp_id, Category.id_comp, GeometricComparison.ConstantComplexF.ConstantComplexDiagonalCoordinates.app_f]
  change _ = ((GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation
    (FrameDiagonalMap.source p k n X Y f hp)
    (P₀ ⋙ (S₀).mapHomologicalComplex (.up ℕ))
    (FrameDiagonalMap.openTransformation p k n X Y f hp)).app
      ((Functor.op F).obj r)).f q
  rw [GeometricComparison.ConstantComplexF.ConstantComplexDiagonalCoordinates.app_f]
  rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.DiagonalCoordinates

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.FixedCoordinates

/-! On principal opens the original diagonal cone is the inverse
of restriction from the fixed native crystalline frame. -/

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X Y f hp U
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X Y f U
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections w n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.diagram w n G
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp) (op U)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X U
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.cone w n
  (Family.center p k n X Y f hp U)
  (Family.cone p k n X Y f hp U)

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def restrictionMap := GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η

instance restrictionMap_isIso : IsIso (restrictionMap p k n X Y f hp U) :=
  Family.fixed_isIso p k n X Y f hp U

/-- Restriction written in the target frame coordinates. -/
def restrictionInTarget := restrictionMap p k n X Y f hp U ≫
  (PrincipalFrameSections.targetIso p k n X Y f hp U).hom

omit [IsProper X.hom] in
private theorem restriction_coordinates_component (q : ℕ) (r : _) :
    ((restrictionInTarget p k n X Y f hp U).f q).app r =
      ((PrincipalFrameSections.map p k n X Y f hp U).f q).app r := by
  change ((GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P η).f q).app r ≫ 𝟙 _ =
    ((GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map S K P
      (PrincipalFrameSections.cone p k n X Y f hp U)).f q).app r ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id, GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.component,
    GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.component, BoundedFrame.FamilySections.Family.cone_app]
  rfl

omit [IsProper X.hom] in
theorem restriction_coordinates : restrictionInTarget p k n X Y f hp U =
      PrincipalFrameSections.map p k n X Y f hp U := by
  apply HomologicalComplex.hom_ext
  intro q
  apply NatTrans.ext
  funext r
  exact restriction_coordinates_component p k n X Y f hp U q r

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.FixedCoordinates

end

end OAI
