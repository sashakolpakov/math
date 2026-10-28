import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionData

/-! # Additive Top Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFraction

noncomputable section

/-! The actual restricted additive top-form map sends the original
local fraction to its signed scalar-weighted bounded residue. -/
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
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (a : Fin g → Γ(X.left,U.val))

variable (O : Y.left.Opens)
  (hO : ∀ i, (Supported.Comparison.opens p k n X Y f U).obj
    (Supported.Comparison.family p k n X U g a i) ≤ O)
  (hcover : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
      ⨆ i, (Supported.Comparison.opens p k n X Y f U).obj
        (Supported.Comparison.family p k n X U g a i))
  (hrows : ∀ q r, ((BoundedSupported.Cech.bicomplex
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)).X q).ExactAt (r+1))
  (hglobal : (Supported.Comparison.opens p k n X Y f U).obj
    (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)

theorem comparison (q : ℕ) : (AdditiveTopFractionData.inputIso p k n X U g a q).hom ≫
    AdditiveTopFractionData.map p k n X Y f hp U I g a O hO hcover hrows hglobal q =
    (AdditiveTopFractionData.forget p k).map (TopFractionBounded.map p k n X Y f hp U I g a
      O hO hcover hrows hglobal q) := by
  dsimp only [AdditiveTopFractionData.inputIso, AdditiveTopFractionData.map, AdditiveTopFractionData.toBounded, TopFractionBounded.map, AdditiveTopFractionData.linearMap, AdditiveTopFractionData.linearDeRhamMap]
  exact BoundedSupported.CoefficientFactor.comparison
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (AdditiveTopFractionData.family p k n X U g a) O hO hcover hrows hglobal (AdditiveTopFractionData.forget p k)
    (PrincipalTopCoordinates.sourceIso p k n X U g)
    (AdditiveTopFractionData.linearMap p k n X Y f hp U I g) (AdditiveTopFractionData.restrictedMap p k n X Y f hp U I g)
    (AdditiveTopFractionData.factorization p k n X Y f hp U I g) q

def input (r : WittVector p k) := (AdditiveTopFractionData.inputIso p k n X U g a (g+g)).hom
  (PrincipalTopFraction.singleClass p k n X Y f hp U g a r)

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

include σ in
theorem fraction (r : WittVector p k) :
    AdditiveTopFractionData.map p k n X Y f hp U I g a O hO hcover hrows hglobal (g+g)
      (input p k n X Y f hp U g a r) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
        SupportedResidue.residue p k n X Y f hp U I g a O
          hO hcover hrows hglobal) := by
  have h := ConcreteCategory.congr_hom
    (comparison p k n X Y f hp U I g a O hO hcover hrows hglobal (g+g))
    (PrincipalTopFraction.singleClass p k n X Y f hp U g a r)
  exact h.trans (TopFractionBounded.fraction p k n X Y f hp U I g a
    O hO hcover hrows hglobal σ r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFraction
