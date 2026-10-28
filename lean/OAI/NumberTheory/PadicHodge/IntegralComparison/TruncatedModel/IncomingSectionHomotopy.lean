import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingHomotopy

/-! # Incoming Section Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionHomotopy

noncomputable section

/-! The actual common-incoming-site homotopy, expressed on the whole
original principal-open section family. -/

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIncomingHomotopy.preimage f₁ U₁
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X₁ Y f₁ U₁
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.restriction p k n X₁ Y f₁ U₁
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n O
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.localSections (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n V O
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.iso (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  w n V O (PrincipalSections.le_chart p k n X₁ Y f₁ U₁)
local notation "F₁" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y f₁ hp₁) U₁
local notation "F₂" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y f₂ hp₂) U₂
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex w n F₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex w n F₂

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def source : ((S).mapHomologicalComplex (.up ℕ)).obj K₁ ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  SectionedIncomingHomotopy.map R S T s (K := K₁) (L := I.cocomplex)
  (IncomingFrame.comparison p k n X₁ Y f₁ hp₁ U₁ I)

def target : ((S).mapHomologicalComplex (.up ℕ)).obj K₂ ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  SectionedIncomingHomotopy.map R S T s (K := K₂) (L := I.cocomplex)
  (LocalIncomingHomotopy.targetMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I)

def frameMap := ((S).mapHomologicalComplex (.up ℕ)).map
  (BoundedFrame.Change.sheafMap
    (BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom)

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X₁)
  (hi : U₁.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X₁ i)

def homotopy : Homotopy (source p k n X₁ Y f₁ hp₁ U₁ I)
    (frameMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e ≫
      target p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I) :=
  SectionedIncomingHomotopy.homotopy R S T s
    (BoundedFrame.Change.sheafMap
      (BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom)
    (IncomingFrame.comparison p k n X₁ Y f₁ hp₁ U₁ I)
    (LocalIncomingHomotopy.targetMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I)
    (LocalIncomingHomotopy.homotopy p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I i hi)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionHomotopy
