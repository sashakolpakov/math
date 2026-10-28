import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointSpectrum

/-! # Scheme Point Underlying -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Underlying points of complex-valued scheme points

This is the genuine map obtained by evaluating a morphism from `Spec ℂ` at its
unique point. It is continuous from the ordinary affine-test topology on complex
points to the Zariski topology of the scheme. Its affine formula is the prime
kernel of the corresponding complex algebra character.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The unique point of the complex base scheme, represented by its zero prime. -/
def SchemePointHomeomorphs.schemeComplexPoints.basePoint : Foundations.Scheme.ProjectiveSpace.complexBase := (⊥ : PrimeSpectrum ℂ)

/-- The underlying scheme point of a morphism from the complex point. -/
def SchemePointHomeomorphs.schemeComplexPoints.underlying (x : SchemePointHomeomorphs.schemeComplexPoints X) : X.left := x.left SchemePointHomeomorphs.schemeComplexPoints.basePoint

/-- Taking the underlying point commutes with a morphism of complex schemes. -/
@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.underlying_map (f : X ⟶ Y) (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map f x) = f.left (SchemePointHomeomorphs.schemeComplexPoints.underlying x) := rfl

/-- On an affine test, the underlying point is the image of the character's prime kernel. -/
@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap (A : CommAlgCat ℂ)
    (f : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A f x) = f.left (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := A) x) := by
  change ((Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A x).left ≫ f.left) SchemePointHomeomorphs.schemeComplexPoints.basePoint = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  change f.left (PrimeSpectrum.comap x.toRingHom (⊥ : PrimeSpectrum ℂ)) = _
  rfl

/-- The actual underlying-point map is continuous for the affine-test topology. -/
@[continuity, fun_prop]
theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying : Continuous (SchemePointHomeomorphs.schemeComplexPoints.underlying (X := X)) := by
  apply (SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineTests _).mpr
  intro A f
  simp only [SchemePointHomeomorphs.schemeComplexPoints.underlying_affinePointMap]
  exact f.left.continuous.comp Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_toPrimeSpectrum

/-- Scheme open sets give open sets of ordinary complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpen_preimage_underlying (U : Set X.left) (hU : IsOpen U) :
    IsOpen (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' U) :=
  hU.preimage SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
