import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionFamilyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindex

/-! # Supported Reindex Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData

noncomputable section

/-! The actual change of a smooth model preserves the principal
support cover, its terminal open, and its section transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X₁ Y f₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X₂ Y f₂ U₂
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

instance reindex_preserves : PreservesFiniteLimits r := by
  change PreservesFiniteLimits (Principal.CoefficientChange.functor e.hom.ambientMap.toRingHom)
  infer_instance

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem opens_eq : F₁ = r ⋙ F₂ :=
  CategoryTheory.Functor.ext (fun t =>
    (PrincipalOpensIso.opens_apply p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e t).symm)
    (fun _ _ _ => Subsingleton.elim _ _)

include e in
omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem terminal_eq :
    (F₁).obj (⊤_ (PrincipalFrame.Index X₁.left U₁)) =
      (F₂).obj (⊤_ (PrincipalFrame.Index X₂.left U₂)) := by
  rw [opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e]
  exact Supported.OrderedCechReindex.terminal_eq Y.left.carrier r F₂

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))

def coefficients : Fin g → Γ(X₂.left, U₂.val) := fun i => e.hom.ambientMap (b i)

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem family_eq :
    (r).obj ∘ Supported.Comparison.family p k n X₁ U₁ g b =
      Supported.Comparison.family p k n X₂ U₂ g
        (coefficients p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b) := rfl

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem rows (q m : ℕ) :
    ((BoundedSupported.Cech.bicomplex w n I (r ⋙ F₂)
      (Supported.Comparison.family p k n X₁ U₁ g b)).X q).ExactAt (m+1) := by
  rw [← opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e]
  exact SupportedRows.exactAt_succ p k n X₁ Y f₁ U₁ I g b q m

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem section_hom :
    ((NatIso.mapHomologicalComplex
      (IncomingSectionReindex.sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
      (.up ℕ)).app I.cocomplex).hom =
    eqToHom (congrArg
      (fun F => Supported.OrderedCechEdge.presheafComplex.{1,0,0,2} R Y.left.carrier F
        (BoundedOpen.FlasqueComplex.complex w n I))
      (opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)) :=
  BoundedSupported.SectionFamilyCoordinates.Family.hom w n I
    (PrincipalSections.opens p k n X₁ Y f₁ U₁)
    (BoundedOpen.IncomingMap.reindexedOpens
      (PrincipalSections.opens p k n X₂ Y f₂ U₂) r)
    (IncomingSectionReindex.family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData
