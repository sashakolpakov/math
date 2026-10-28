import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientComponent
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PDFrameNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDFrameIso

/-! # Principal PD Naturality -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDNaturality.Square

/-! The original principal PD comparison commutes with the native
principal-family isomorphism, at each degree and each localization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₁.left U₁.val U₁.property
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₂.left U₂.val U₂.property
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates.originalFunctor p k Y
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded (OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y) n

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem component (q : ℕ) (r : C) :
    ((Principal.Comparison.nativePDMap p k n X₁ Y f₁ hp₁ U₁).f q).app (op r) ≫
      ((N).map ((B).hom.app r).op).f q =
    ((Supported.PDFrameIso.complexIso p k Y e).hom.f q).app (op r) ≫
      ((Principal.Comparison.nativePDMap p k n X₂ Y f₂ hp₂ U₂).f q).app (op ((R).obj r)) := by
  have hs := congrArg (fun a => a.app r)
    (PrincipalTransport.principal_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  change (S).hom.app r ≫ PrincipalFrame.map p k n X₁ Y f₁ hp₁ U₁ r =
    PrincipalFrame.map p k n X₂ Y f₂ hp₂ U₂ ((R).obj r) ≫
      CrystallinePrincipal.Iso.map p k Y e r at hs
  have hd := congrArg (fun a => (D).map a.op) hs
  simp only [op_comp, Functor.map_comp] at hd
  have hdq := congrArg (fun a => a.f q) hd
  have hn := congrArg (fun a => a.f q)
    (PDFrameNaturality.naturality p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂
      ((P₁).obj r) ((P₂).obj ((R).obj r)) ((S).app r))
  rw [PrincipalCoefficientComponent.PD.nativePDMap_component,
    PrincipalCoefficientComponent.PD.nativePDMap_component]
  calc
    _ = ((D).map (PrincipalFrame.map p k n X₁ Y f₁ hp₁ U₁ r).op).f q ≫
        (((D).map ((S).hom.app r).op).f q ≫
          (PrincipalCoefficientComponent.PD.coordinate p k n X₂ Y f₂ hp₂ U₂ ((R).obj r)).f q) := by
      rw [Category.assoc]
      exact congrArg (fun z => ((D).map (PrincipalFrame.map p k n X₁ Y f₁ hp₁ U₁ r).op).f q ≫ z) hn.symm
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (fun z => z ≫
        (PrincipalCoefficientComponent.PD.coordinate p k n X₂ Y f₂ hp₂ U₂ ((R).obj r)).f q) hdq

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDNaturality.Square

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDNaturality

/-! Naturality of the actual native principal PD cochain map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X₁.left U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFamilyIso.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "P₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₁.left U₁.val U₁.property
local notation "P₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X₂.left U₂.val U₂.property
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDComplexCoordinates.originalFunctor p k Y
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded (OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y) n

def restriction :
    ((PrincipalFrame.Index X₂.left U₂)ᵒᵖ ⥤ ModuleCat (WittVector p k)) ⥤
    (Cᵒᵖ ⥤ ModuleCat (WittVector p k)) :=
  (Functor.whiskeringLeft _ _ _).obj (R).op

instance restriction_additive : (restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).Additive where
  map_add := rfl

def diagramIso : Principal.Comparison.nativeDiagram p k n X₁ Y f₁ hp₁ U₁ ≅
    (R).op ⋙ Principal.Comparison.nativeDiagram p k n X₂ Y f₂ hp₂ U₂ :=
  Functor.isoWhiskerRight (NatIso.op (B)) (N)

def reindexedMap : Supported.PDFrameIso.complex p k Y e ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      ((R).op ⋙ Principal.Comparison.nativeDiagram p k n X₂ Y f₂ hp₂ U₂) :=
  ((restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).mapHomologicalComplex (.up ℕ)).map
    (Principal.Comparison.nativePDMap p k n X₂ Y f₂ hp₂ U₂)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem naturality :
    Principal.Comparison.nativePDMap p k n X₁ Y f₁ hp₁ U₁ ≫
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (diagramIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom =
    (Supported.PDFrameIso.complexIso p k Y e).hom ≫
      reindexedMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  exact Square.component p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e q r.unop

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalPDNaturality

end

end OAI
