import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FractionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue

/-! # Supported Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedFraction.Integral

noncomputable section

/-! The actual integral sheaf-form fraction reaches the original bounded
crystalline residue through the canonical principal comparison. -/

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

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) (a : Fin g → Γ(X.left, U.val)) (O : Y.left.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFrame.Index X.left U
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.opens p k n X Y f U
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Supported.Comparison.family p k n X U g a
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y

variable (hO : ∀ i, (Supported.Comparison.opens p k n X Y f U).obj
    (Supported.Comparison.family p k n X U g a i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X Y f U).obj
        (Supported.Comparison.family p k n X U g a i))
  (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)).X q).ExactAt (r + 1))
  (hglobal : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

def toBounded :=
  HomologicalComplex.homologyMap
      (AugmentedOrdered.CechCoefficientTop.totalMap V
        (FractionClass.Integral.iso p k n X Y f hp U σ).inv) (g + g) ≫
    Supported.Comparison.toBounded p k n X Y f hp U I g a O
      hO hcover hrows hglobal (g + g)

theorem fraction (r : WittVector p k) :
    toBounded p k n X Y f hp U σ I g a O hO hcover hrows hglobal
        (FractionClass.Integral.fractionClass p k n X Y f hp U σ g a r) =
      (⟨r⟩ : R) • SupportedResidue.residue p k n X Y f hp U I g a O
        hO hcover hrows hglobal := by
  have h := FractionClass.Integral.inverse_class p k n X Y f hp U σ g a r
  exact (congrArg
    (Supported.Comparison.toBounded p k n X Y f hp U I g a O
      hO hcover hrows hglobal (g + g)) h).trans
    ((Supported.Comparison.toBounded p k n X Y f hp U I g a O
      hO hcover hrows hglobal (g + g)).hom.map_smul (⟨r⟩ : R)
      (ResidueClass.residueClass p k n X Y f hp U g a))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedFraction.Integral
