import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Quadratic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Inversion Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The graph of inversion carries the tensor square of the canonical
graph bundle. Its section polynomial and all positive tensor powers are
therefore uniform over every field, without a chosen polarization bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
def PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundle {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) : Line.Bundles.LineBundle A.abelian.scheme.left :=
  A.graphBundle.tensor (A.graphBundle.pullback ι[A.abelian.scheme].left)

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundleIso :
    A.inversionGraphBundle.sheaf ≅ (A.graphBundle.tensorPower 2).sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso (Iso.refl A.graphBundle.sheaf) A.graphBundle_symmetric.some ≪≫
    Tensor.Bifunctor.tensorModuleMapIso A.graphBundle.tensorPowerOneIso.symm A.graphBundle.tensorPowerOneIso.symm ≪≫
      (A.graphBundle.tensorPowerAddIso 1 1).symm

def PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundlePowerIso (m : ℕ) :
    (A.inversionGraphBundle.tensorPower m).sheaf ≅ (A.graphBundle.tensorPower (m * 2)).sheaf :=
  (TensorPower.Maps.tensorPowerFunctor A.abelian.scheme.left m).mapIso A.inversionGraphBundleIso ≪≫
    (A.graphBundle.tensorPowerComposeIso m 2).symm

theorem PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundle_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    A.inversionGraphBundle.HasSectionHilbertPolynomial A.abelian.scheme.hom
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C (2 : ℚ) * Polynomial.X)) :=
  (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso A.abelian.scheme.hom
    A.inversionGraphBundle (A.graphBundle.tensorPower 2) A.inversionGraphBundleIso _).mpr
      (A.graphBundle_positivePower_normalized_hilbertPolynomial hg hN hNk 2 (by decide))

theorem PolarizationData.PolarizedAbelianWithFullLevel.inversionGraphBundle_positivePower_hilbertPolynomial
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (m : ℕ) (hm : 0 < m) :
    (A.inversionGraphBundle.tensorPower m).HasSectionHilbertPolynomial A.abelian.scheme.hom
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp (Polynomial.C ((m * 2 : ℕ) : ℚ) * Polynomial.X)) :=
  (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso A.abelian.scheme.hom
    (A.inversionGraphBundle.tensorPower m) (A.graphBundle.tensorPower (m * 2))
      (A.inversionGraphBundlePowerIso m) _).mpr
        (A.graphBundle_positivePower_normalized_hilbertPolynomial hg hN hNk (m * 2)
          (Nat.mul_pos hm (by decide)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
