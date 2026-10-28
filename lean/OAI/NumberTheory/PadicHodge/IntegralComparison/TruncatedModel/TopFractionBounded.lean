import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopFraction

/-! # Top Fraction Bounded -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopFractionBounded

noncomputable section

/-! The original single-top-form class reaches bounded crystalline
cohomology through the genuine restricted sheaf map, retaining the
interchange sign and its arbitrary original residue coefficient. -/
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
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] (a : Fin g → Γ(X.left, U.val)) (O : Y.left.Opens)
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

def map (q : ℕ) :=
  BoundedSupported.Cech.map (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)
    O hO hcover hrows hglobal
    ((single _ (.up ℕ) g).obj (PrincipalTopSingle.coefficient p k n X U g))
    (PrincipalTopSingle.map p k n X U g ≫
      PrincipalSheaf.Comparison.map p k n X Y f hp U I) q

theorem factorization (q : ℕ) :
    TopFractionBounded.map p k n X Y f hp U I g a O hO hcover hrows hglobal q =
      homologyMap (AugmentedOrdered.CechCoefficientTop.totalMap
        (Supported.Comparison.family p k n X U g a)
        (PrincipalTopSingle.map p k n X U g)) q ≫
      SheafSupportedFraction.toBounded
        p k n X Y f hp U I g a O hO hcover hrows hglobal q :=
  BoundedSupported.CechPrecompose.comparison
    (Witt.Crystalline.wittStructureMap p k Y) n I
    (Supported.Comparison.opens p k n X Y f U)
    (Supported.Comparison.family p k n X U g a)
    O hO hcover hrows hglobal
    (PrincipalTopSingle.map p k n X U g)
    (PrincipalSheaf.Comparison.map p k n X Y f hp U I) q

variable (σ : Type) [LinearOrder σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n) (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

include σ in
theorem fraction (r : WittVector p k) :
    TopFractionBounded.map p k n X Y f hp U I g a O hO hcover hrows hglobal (g+g)
      (PrincipalTopFraction.singleClass p k n X Y f hp U g a r) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector p k)) •
        SupportedResidue.residue p k n X Y f hp U I g a O
          hO hcover hrows hglobal) := by
  rw [factorization, ConcreteCategory.comp_apply,
    PrincipalTopFraction.image p k n X Y f hp U g a σ r]
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun x =>
    ((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) • x)
    (SheafSupportedFraction.fraction
      p k n X Y f hp U I g a O hO hcover hrows hglobal σ r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopFractionBounded
