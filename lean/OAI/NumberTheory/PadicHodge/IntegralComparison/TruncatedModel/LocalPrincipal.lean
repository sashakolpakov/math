import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalOpenFunctorEq
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality

/-! # Local Principal -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal.Sections
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! The actual local principal comparison is natural under a change
of smooth lift, after the literal reindexing of its geometric opens. -/

open Opposite

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "O₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₁ Y f₁ U₁
local notation "O₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₂ Y f₂ U₂
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₁ Y f₁ hp₁ U₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₂ Y f₂ hp₂ U₂
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₁ Y f₁ hp₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₂ Y f₂ hp₂ U₂
local notation "ρ₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₁ Y f₁ hp₁ U₁
local notation "ρ₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₂ Y f₂ hp₂ U₂
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family.frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "ρ" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family.cone p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections w n O₁
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def sourceMap := by
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₁ G₁ F₁ ρ₁) :=
    PrincipalIn.Family.fixed_isIso p k n X₁ Y f₁ hp₁ U₁
  exact BoundedFrame.LocalMap.map w n O₁ G₁ F₁ ρ₁

def targetMap := by
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₁ G F₂ ρ) :=
    PrincipalTransportedFamily.Family.restriction_isIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
  exact BoundedFrame.LocalMap.map w n O₁ G F₂ ρ

def baseMap := ((S).mapHomologicalComplex (.up ℕ)).map
  ((Q).map (PrincipalTransportedFamily.Family.baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom)

def absoluteMap := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ)
  (Functor.whiskerRight
    (PrincipalTransportedFamily.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom
    (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w n))

def sectionChange :=
  ((NatIso.mapHomologicalComplex
    (BoundedFrame.LocalMap.sectionsIso w n O₁ ((R).op ⋙ O₂)
      (PrincipalOpenFunctorEq.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm)
    (.up ℕ)).app ((Q).obj F₂)).hom

def reindexedMap := ((H).mapHomologicalComplex (.up ℕ)).map
  (sourceMap p k n X₂ Y f₂ hp₂ U₂)

omit [IsProper X₁.hom] [IsProper X₂.hom] [X₂.left.IsSeparated] in
theorem naturality : sourceMap p k n X₁ Y f₁ hp₁ U₁ ≫
    baseMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e =
      absoluteMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ≫
        targetMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e :=
  PrincipalTransportedFamily.Family.naturality p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

end

/-! The actual local principal comparison is natural under a change
of smooth lift, after the literal reindexing of its geometric opens. -/

open Opposite

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "O₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₁ Y f₁ U₁
local notation "O₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X₂ Y f₂ U₂
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₁ Y f₁ hp₁ U₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₂ Y f₂ hp₂ U₂
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₁ Y f₁ hp₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₂ Y f₂ hp₂ U₂
local notation "ρ₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₁ Y f₁ hp₁ U₁
local notation "ρ₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₂ Y f₂ hp₂ U₂
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family.frames p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "ρ" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTransportedFamily.Family.cone p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections w n O₁
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

attribute [local instance] globalSeparated

abbrev target_coordinates := by
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₁ ((R).op ⋙ G₂) F₂
      (BoundedFrame.SectionReindex.cone w n (R).op G₂ F₂ ρ₂)) :=
    PrincipalTransportedFamily.Family.restriction_isIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
  let : IsIso (BoundedFrame.LocalMap.restriction w n O₂ G₂ F₂ ρ₂) :=
    PrincipalIn.Family.fixed_isIso p k n X₂ Y f₂ hp₂ U₂
  exact BoundedFrame.LocalReindex.coordinates w n (R).op O₂ G₂ F₂ ρ₂ O₁
    (PrincipalOpenFunctorEq.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal.Sections

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal.PDNaturality

/-! The actual local PD-to-frame comparison commutes with change of
smooth lift, including its native coefficient map and reindexing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose {C : Type*} [Category C] {K A F F' A' K' Q : C}
    (a : K ⟶ A) (l : A ⟶ F) (b : F ⟶ F') (e : F' ⟶ Q)
    (q : A ⟶ A') (t : A' ⟶ F') (k : K ⟶ K') (a' : K' ⟶ A') (l' : A' ⟶ Q)
    (h₁ : l ≫ b = q ≫ t) (h₂ : t ≫ e = l') (h₃ : a ≫ q = k ≫ a') :
    (a ≫ l) ≫ (b ≫ e) = k ≫ (a' ≫ l') := by
  calc
    (a ≫ l) ≫ (b ≫ e) = (a ≫ (l ≫ b)) ≫ e := by simp only [Category.assoc]
    _ = (a ≫ (q ≫ t)) ≫ e := by rw [h₁]
    _ = (a ≫ q) ≫ (t ≫ e) := by simp only [Category.assoc]
    _ = (k ≫ a') ≫ l' := by rw [h₂, h₃]
    _ = k ≫ (a' ≫ l') := Category.assoc _ _ _

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

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.restriction p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalCoefficientNaturality.sourceIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

def map := Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁ ≫
  Sections.sourceMap p k n X₁ Y f₁ hp₁ U₁

def transport := Sections.baseMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ≫
  Sections.sectionChange p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem absolute_coordinates :
    Sections.absoluteMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e =
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ)
        (PrincipalCoefficientNaturality.diagramIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  rfl

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem coefficient_square : Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁ ≫
    Sections.absoluteMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e =
      (s).hom ≫ PrincipalCoefficientNaturality.reindexedMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e := by
  rw [absolute_coordinates]
  exact PrincipalCoefficientNaturality.naturality p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPrincipal.PDNaturality

end

end OAI
