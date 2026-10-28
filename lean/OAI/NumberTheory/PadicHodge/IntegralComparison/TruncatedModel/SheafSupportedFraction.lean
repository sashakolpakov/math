import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSupportedIntegralSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechPrecompose

/-! # Sheaf Supported Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSupportedFraction

noncomputable section

/-! The genuine sheaf comparison sends the literal integral fraction
to the original bounded crystalline residue. The map is the actual
restricted sheaf map, with the original support-forgetting construction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
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
  (hO : ∀ i, (Supported.Comparison.opens p k n X Y f U).obj
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

def toBounded (q : ℕ) :=
  BoundedSupported.Cech.map (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)
    O hO hcover hrows hglobal (FractionClass.Integral.target p k n X U)
    (PrincipalSheaf.Comparison.map p k n X Y f hp U I) q

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

theorem comparison :
    toBounded p k n X Y f hp U I g a O hO hcover hrows hglobal (g+g) =
      SupportedFraction.Integral.toBounded p k n X Y f hp U σ I g a O
        hO hcover hrows hglobal := by
  let e := FractionClass.Integral.iso p k n X Y f hp U σ
  have he : e.inv ≫ Principal.Comparison.map p k n X Y f hp U I =
      PrincipalSheaf.Comparison.map p k n X Y f hp U I := by
    rw [← PrincipalSheaf.Comparison.comparison p k n X Y f hp U I σ]
    exact e.inv_hom_id_assoc _
  have h := BoundedSupported.CechPrecompose.comparison
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)
    O hO hcover hrows hglobal e.inv
    (Principal.Comparison.map p k n X Y f hp U I) (g+g)
  rw [he] at h
  exact h

theorem fraction (r : WittVector p k) :
    toBounded p k n X Y f hp U I g a O hO hcover hrows hglobal (g+g)
      (FractionClass.Integral.fractionClass p k n X Y f hp U σ g a r) =
    (⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
      SupportedResidue.residue p k n X Y f hp U I g a O
        hO hcover hrows hglobal := by
  rw [comparison p k n X Y f hp U I g a O hO hcover hrows hglobal σ]
  exact SupportedFraction.Integral.fraction
    p k n X Y f hp U σ I g a O hO hcover hrows hglobal r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafSupportedFraction
