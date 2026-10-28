import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentParameterBaseChange
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Containment Affine Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentAffineCharts

noncomputable section

/-! Every affine chart of a locally noetherian parameter scheme has
an actual closed locus representing the same native containment condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S)

def affineParameterChart (i : B.left.affineOpenCover.I₀) : Over S :=
  Over.mk (B.left.affineOpenCover.f i ≫ B.hom)

def affineParameterChartInclusion (i : B.left.affineOpenCover.I₀) : affineParameterChart B i ⟶ B :=
  Over.homMk (B.left.affineOpenCover.f i) rfl

instance affineParameterChartInclusion_isOpenImmersion (i : B.left.affineOpenCover.I₀) :
    IsOpenImmersion (affineParameterChartInclusion B i).left :=
  inferInstanceAs (IsOpenImmersion (B.left.affineOpenCover.f i))

instance affineParameterChart_noetherian [IsLocallyNoetherian B.left] (i : B.left.affineOpenCover.I₀) :
    IsNoetherianRing (B.left.affineOpenCover.X i) :=
  isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (B.left.affineOpenCover.f i))

namespace GradedHilbert

variable (n : ℕ) [IsLocallyNoetherian B.left]
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B)
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B).IdealSheafData)

def nativeContainmentChart (i : B.left.affineOpenCover.I₀) : Over S :=
  AffineContainment.GradedHilbert.nativeAffineContainmentScheme n (B.left.affineOpenCover.X i) (B.left.affineOpenCover.f i ≫ B.hom)
    (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i) F)
    (K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i)))

def nativeContainmentChartInclusion (i : B.left.affineOpenCover.I₀) :
    nativeContainmentChart B n F K i ⟶ affineParameterChart B i :=
  AffineContainment.GradedHilbert.nativeAffineContainmentInclusion n (B.left.affineOpenCover.X i) (B.left.affineOpenCover.f i ≫ B.hom)
    (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i) F)
    (K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i)))

instance nativeContainmentChartInclusion_isClosedImmersion (i : B.left.affineOpenCover.I₀) :
    IsClosedImmersion (nativeContainmentChartInclusion B n F K i).left :=
  AffineContainment.GradedHilbert.nativeAffineContainmentInclusion_isClosedImmersion n (B.left.affineOpenCover.X i)
    (B.left.affineOpenCover.f i ≫ B.hom)
    (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i) F)
    (K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i)))

theorem nativeContainmentChart_all_tests (i : B.left.affineOpenCover.I₀)
    (T : Over S) (x : T ⟶ affineParameterChart B i) :
    x ≫ affineParameterChartInclusion B i ∈
      (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj (.op T) ↔
      ∃! y : T ⟶ nativeContainmentChart B n F K i, y ≫ nativeContainmentChartInclusion B n F K i = x :=
  (Ideal.ContainmentParameterBaseChange.Hilbert.idealContainmentParameter_baseChange (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
    (affineParameterChartInclusion B i) x).symm.trans
    (AffineContainmentRepresentation.GradedHilbert.nativeAffineContainmentInclusion_all_tests n (B.left.affineOpenCover.X i)
      (B.left.affineOpenCover.f i ≫ B.hom)
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i) F)
      (K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (affineParameterChartInclusion B i))) T x)

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentAffineCharts
