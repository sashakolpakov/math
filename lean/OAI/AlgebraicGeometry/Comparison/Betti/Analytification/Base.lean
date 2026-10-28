import OAI.AlgebraicGeometry.Betti.Scheme
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointSpectrum

/-! # Base -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Base

noncomputable section

/-! The natural map from actual complex points with their analytic topology
to the underlying Zariski space. This is the topological part of the
analytification morphism needed for algebraic de Rham comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def complexBasePoint : Foundations.Scheme.ProjectiveSpace.complexBase :=
  (⟨⊥, by infer_instance⟩ : PrimeSpectrum ℂ)

def underlyingZariskiPoint (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : X.left :=
  x.left complexBasePoint

theorem underlyingZariskiPoint_affineTest (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    underlyingZariskiPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f x) =
      f.left (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) := by
  change ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x).left ≫ f.left) complexBasePoint = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left A x]
  rfl

theorem underlyingZariskiPoint_continuous (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Continuous (underlyingZariskiPoint X) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A f
  have h := f.left.continuous.comp (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_toPrimeSpectrum (A := A))
  exact h.congr (fun x => (underlyingZariskiPoint_affineTest X A f x).symm)

def analytificationMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Betti.Scheme.schemePointSpace X ⟶ TopCat.of X.left :=
  TopCat.ofHom ⟨underlyingZariskiPoint X, underlyingZariskiPoint_continuous X⟩

theorem analytificationMap_naturality {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f ≫ analytificationMap Y =
      analytificationMap X ≫ TopCat.ofHom ⟨f.left, f.left.continuous⟩ := by
  apply TopCat.ext
  intro x
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Base
