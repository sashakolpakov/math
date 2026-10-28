import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData

/-! # Supported Reindex Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry

noncomputable section

/-! The actual principal support cover and bounded resolution rows
transport along the isomorphism of smooth crystalline frames. -/

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

variable (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val)) (O : Y.left.Opens)

local notation "b₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexData.coefficients p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b

abbrev sourceFamily := Supported.Comparison.family.{0} p k n X₁ U₁ g b
abbrev targetFamily := Supported.Comparison.family.{0} p k n X₂ U₂ g b₂

local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.sourceFamily p k n X₁ U₁ g b
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry.targetFamily p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e g b

variable (hO : ∀ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (Supported.Comparison.family.{0} p k n X₁ U₁ g b i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
        (Supported.Comparison.family.{0} p k n X₁ U₁ g b i))
  (hglobal : (Supported.Comparison.opens p k n X₁ Y f₁ U₁).obj
    (⊤_ (PrincipalFrame.Index X₁.left U₁)) ⊔ O = ⊤)

include hO in
omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem below : ∀ i, (F₂).obj (V₂ i) ≤ O := by
  intro i
  change (F₂).obj ((r).obj (V i)) ≤ O
  exact (congrArg (fun F => F.obj (V i))
    (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)).symm.le.trans (hO i)

include hcover in
omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem cover : (F₂).obj (⊤_ (PrincipalFrame.Index X₂.left U₂)) ⊓ O ≤
    ⨆ i, (F₂).obj (V₂ i) := by
  apply (inf_le_inf
    (SupportedReindexData.terminal_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm.le
    (le_refl O)).trans
  apply hcover.trans
  apply iSup_mono
  intro i
  exact (congrArg (fun F => F.obj (V i))
    (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)).le

include e hglobal in
omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem global : (F₂).obj (⊤_ (PrincipalFrame.Index X₂.left U₂)) ⊔ O = ⊤ := by
  rw [← SupportedReindexData.terminal_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e]
  exact hglobal

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem rows (q m : ℕ) :
    ((BoundedSupported.Cech.bicomplex w n I F₂ ((r).obj ∘ V)).X q).ExactAt (m+1) :=
  SupportedRows.exactAt_succ p k n X₂ Y f₂ U₂ I g b₂ q m

omit [IsProper X₁.hom] [X₁.left.IsSeparated] [IsProper X₂.hom] [X₂.left.IsSeparated] [IsSeparated Y.hom] in
theorem section_inv :
    ((NatIso.mapHomologicalComplex
      (IncomingSectionReindex.sectionIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
      (.up ℕ)).app I.cocomplex).inv =
    eqToHom (congrArg
      (fun F => Supported.OrderedCechEdge.presheafComplex.{1,0,0,2} R Y.left.carrier F
        (BoundedOpen.FlasqueComplex.complex w n I))
      (SupportedReindexData.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm) :=
  BoundedSupported.SectionFamilyCoordinates.Family.inv w n I
    (PrincipalSections.opens p k n X₁ Y f₁ U₁)
    (BoundedOpen.IncomingMap.reindexedOpens
      (PrincipalSections.opens p k n X₂ Y f₂ U₂) r)
    (IncomingSectionReindex.family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedReindexGeometry
