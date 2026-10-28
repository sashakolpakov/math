import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedSection

/-! # Model Supported Integral Section -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSupportedIntegralSection

noncomputable section

/-! The literal integral logarithmic fraction at a closed section reaches
the original bounded residue. Its support cover and row exactness are
derived from the section and the original injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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
  (s : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X.left)
  [IsClosedImmersion s]
  (g : ℕ) (a : Fin g → Γ(X.left, U.val))
  (ha : Ideal.span (Set.range a) = s.ker.ideal U)
  (hs : ⊤ ≤ s ⁻¹ᵁ U.val)

abbrev toBounded :=
  SupportedFraction.Integral.toBounded p k n X Y f hp U σ I g a
    (SupportedSection.punctured p k n X Y f s)
    (SupportedSection.below p k n X Y f U s g a ha)
    (SupportedSection.cover p k n X Y f U s g a ha)
    (SupportedRows.exactAt_succ p k n X Y f U I g a)
    (SupportedSection.global p k n X Y f U s hs)

abbrev fraction (r : WittVector p k) :=
  SupportedFraction.Integral.fraction p k n X Y f hp U σ I g a
    (SupportedSection.punctured p k n X Y f s)
    (SupportedSection.below p k n X Y f U s g a ha)
    (SupportedSection.cover p k n X Y f U s g a ha)
    (SupportedRows.exactAt_succ p k n X Y f U I g a)
    (SupportedSection.global p k n X Y f U s hs) r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelSupportedIntegralSection
