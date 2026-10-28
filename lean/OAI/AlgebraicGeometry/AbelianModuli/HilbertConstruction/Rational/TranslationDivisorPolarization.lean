import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorPolarization
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseIdentification

/-! # Translation Divisor Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual translation quotient induces the identity-normalized
original line. Compare that line with the zero normalization used by the
raw graph-power locus, and assemble its divisor's original polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- The two actual normalizations differ only by the construction of the
tensor inverse of the line pulled back from the base. -/
def Rational.TranslationDivisorPolarization.identityNormalizationComparison
    {S : Scheme} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).sheaf ≅ (A.zeroNormalizedBundle L).sheaf := by
  let B := L.pullback η[A.scheme].left
  let M := B.pullback A.scheme.hom
  let R := B.reciprocalFrameBundle.pullback A.scheme.hom
  let eMR : (M.tensor R).sheaf ≅ Line.Bundles.structureModule A.scheme.left :=
    (Line.Bundles.LineBundle.tensorBaseChangeIso A.scheme.hom B B.reciprocalFrameBundle).symm ≪≫
      (Scheme.Modules.pullback A.scheme.hom).mapIso B.tensorReciprocalFrameIso ≪≫
      Line.Bundles.structureModulePullbackIso A.scheme.hom
  let e : (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual M).sheaf ≅ R.sheaf :=
    Classical.choice (Line.Bundles.LineBundle.iso_of_common_tensor_inverse
      (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual M) R M
      ⟨Picard.Homomorphisms.LineBundleEvaluation.Construction.lineBundleEvaluationIso M⟩ ⟨eMR⟩)
  exact Tensor.ProductSheaf.tensorModuleCongr (Iso.refl L.sheaf) e

/-- Recover the normalized inducing formula directly from the actual
Poincare pullback isomorphism supplied by the translation quotient. -/
def Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (m : A.scheme ⟶ D.abelian.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left)
    (recover : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf) :
    (((D.poincareAt m).tensor
      ((A.zeroNormalizedBundle L).pullback (fst A.scheme A.scheme).left)).tensor
      ((A.zeroNormalizedBundle L).pullback (snd A.scheme A.scheme).left)).sheaf ≅
        ((A.zeroNormalizedBundle L).pullback μ[A.scheme].left).sheaf := by
  let N := Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.identityNormalizedLine A L
  have r : (D.poincareAt m).sheaf ≅ (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf := by
    rw [tensorHom_id] at recover
    exact recover
  let e : (((D.poincareAt m).tensor (N.pullback (fst A.scheme A.scheme).left)).tensor
      (N.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (N.pullback μ[A.scheme].left).sheaf :=
    Tensor.ProductSheaf.tensorModuleCongr (Tensor.ProductSheaf.tensorModuleCongr r (Iso.refl _)) (Iso.refl _) ≪≫
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_formula A L).some
  exact Rational.DivisorPolarization.inducingFormulaLineIso D m (Rational.TranslationDivisorPolarization.identityNormalizationComparison A L) e

/-- The actual translation quotient and the raw graph comparison give
the original polarization on its rational base. -/
def PolarizationData.Polarization.ofAmpleTranslationDivisor
    {S : Scheme} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (p : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf)
    (hp : A.multiplication (2 * d) ≫ p.hom = m)
    (eG : (A.zeroNormalizedBundle L).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D p.hom).tensorPower d).sheaf) : PolarizationData.Polarization D δ :=
  PolarizationData.Polarization.ofAmpleNormalizedRationalDivisorGraphPower D p δ hδ qS d hd m L hL
    (Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m L recover) hp eG

/-- This form matches the raw graph-power parameter over any test
scheme, with ampleness required only for the original affine-base line. -/
def PolarizationData.Polarization.ofBaseChangedAmpleTranslationDivisor
    {S T : Scheme} [IsAffine S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) (b : T ⟶ S)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback b) (D.abelian.pullback b))
    (δ : Fin g → ℕ) (hδ : p.HasPolarizationType δ)
    (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf)
    (hp : (A.pullback b).multiplication (2 * d) ≫ p.hom = (Over.pullback b).map m)
    (eG : ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom b)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback b) p.hom).tensorPower d).sheaf) :
    PolarizationData.Polarization (D.pullback b) δ :=
  PolarizationData.Polarization.ofBaseChangedNormalizedRationalDivisorGraphPower D b p δ hδ qS d hd m L hL
    (Rational.TranslationDivisorPolarization.translationDifferenceNormalizedInducingFormula D m L recover) hp eG

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
