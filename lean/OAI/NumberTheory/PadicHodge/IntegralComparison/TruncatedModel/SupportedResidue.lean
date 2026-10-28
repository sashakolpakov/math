import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueClass

/-! # Supported Residue -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue

/-! The local residue cocycle gives a class in the original bounded
crystalline group, independent of lifts of the residual parameters. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (O : Y.left.Opens)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X Y f U
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.family p k n X U g a
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

def residue (hO : ∀ i, (F).obj (V i) ≤ O)
    (hcover : (F).obj (⊤_ C) ⊓ O ≤ ⨆ i, (F).obj (V i))
    (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex w n I F V).X q).ExactAt (r + 1))
    (hglobal : (F).obj (⊤_ C) ⊔ O = ⊤) :=
  Supported.Comparison.toBounded p k n X Y f hp U I g a O
    hO hcover hrows hglobal (g + g)
    (ResidueClass.residueClass p k n X Y f hp U g a)

def changedResidue (hO : ∀ i, (F).obj (V i) ≤ O)
    (hcover : (F).obj (⊤_ C) ⊓ O ≤ ⨆ i, (F).obj (V i))
    (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex w n I F V).X q).ExactAt (r + 1))
    (hglobal : (F).obj (⊤_ C) ⊔ O = ⊤)
    (b : Fin g → Γ(X.left, U.val))
    (hab : ∀ i, (Q).thickening.reduction (b i) = (Q).thickening.reduction (a i)) :=
  Supported.Comparison.toBounded p k n X Y f hp U I g a O
    hO hcover hrows hglobal (g + g)
    (ResidueClass.changedResidueClass p k n X Y f hp U g a b hab)

theorem changedResidue_eq (hO : ∀ i, (F).obj (V i) ≤ O)
    (hcover : (F).obj (⊤_ C) ⊓ O ≤ ⨆ i, (F).obj (V i))
    (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex w n I F V).X q).ExactAt (r + 1))
    (hglobal : (F).obj (⊤_ C) ⊔ O = ⊤)
    (b : Fin g → Γ(X.left, U.val))
    (hab : ∀ i, (Q).thickening.reduction (b i) = (Q).thickening.reduction (a i)) :
    changedResidue p k n X Y f hp U I g a O hO hcover hrows hglobal b hab =
      residue p k n X Y f hp U I g a O hO hcover hrows hglobal :=
  congrArg (Supported.Comparison.toBounded p k n X Y f hp U I g a O
    hO hcover hrows hglobal (g + g))
    (ResidueClass.changedResidueClass_eq p k n X Y f hp U g a b hab)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue.Congruence

/-! Literal equality of the parameters and support open identifies
the original residue maps, independently of the proofs of their cover
and row conditions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ)

abbrev Below (a : Fin g → Γ(X.left,U.val)) (O : Y.left.Opens) : Prop :=
  ∀ i : ULift.{0} (Fin g), (Supported.Comparison.opens p k n X Y f U).obj
    (Supported.Comparison.family p k n X U g a i) ≤ O

abbrev Cover (a : Fin g → Γ(X.left,U.val)) (O : Y.left.Opens) : Prop :=
  (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
      ⨆ i : ULift.{0} (Fin g), (Supported.Comparison.opens p k n X Y f U).obj
        (Supported.Comparison.family p k n X U g a i)

abbrev Rows (a : Fin g → Γ(X.left,U.val)) : Prop :=
  ∀ q r, ((BoundedSupported.Cech.bicomplex (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)).X q).ExactAt (r+1)

abbrev Global (O : Y.left.Opens) : Prop :=
  (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤

theorem congr (a b : Fin g → Γ(X.left,U.val)) (hab : a=b)
    (O P : Y.left.Opens) (hOP : O=P)
    (haO : Below p k n X Y f U g a O) (hbP : Below p k n X Y f U g b P)
    (haC : Cover p k n X Y f U g a O) (hbC : Cover p k n X Y f U g b P)
    (haR : Rows p k n X Y f U I g a) (hbR : Rows p k n X Y f U I g b)
    (haG : Global p k n X Y f U O) (hbG : Global p k n X Y f U P) :
    residue p k n X Y f hp U I g a O haO haC haR haG =
      residue p k n X Y f hp U I g b P hbP hbC hbR hbG := by
  subst b
  subst P
  rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue.Congruence

end

end OAI
