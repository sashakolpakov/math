import OAI.AlgebraicGeometry.Foundations.Scheme.PresentationComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Presented Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.PresentedComplexPoints

noncomputable section

/-!
# Complex points in a native algebra presentation

This transports polynomial-quotient coordinates to an arbitrary complex algebra
using mathlib's proved quotient isomorphism for `Algebra.Presentation`. Its
coordinates are the values of the presentation's actual generators. The formulas
also describe arbitrary algebra maps by polynomials in target generators.
-/

universe u v w u' v' w'

variable {S : Type u} [CommRing S] [Algebra ℂ S]
variable {ι : Type v} {σ : Type w}

/-- The presentation kernel and its specified generating relations have the same solutions. -/
def presentationKernelRelationsEquiv (P : Algebra.Presentation ℂ S ι σ) :
    MvPolynomial.zeroLocus ℂ P.ker ≃
      {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0} where
  toFun z := ⟨z.val, fun j => z.property (P.relation j) (P.relation_mem_ker j)⟩
  invFun z := ⟨z.val, by
    rw [← P.span_range_relation_eq_ker, MvPolynomial.zeroLocus_span]
    rintro p ⟨j, rfl⟩
    exact z.property j⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A native presentation identifies the actual algebra's complex points with its equations. -/
def presentedComplexPointsEquiv (P : Algebra.Presentation ℂ S ι σ) :
    AffineComplexPoints.affineComplexPoints S ≃
      {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0} :=
  (AffineComplexPoints.affineComplexPoints.comapHomeomorph (P.quotientEquiv.restrictScalars ℂ)).toEquiv.trans
    ((PresentationComplexPoints.presentationComplexPointsEquiv P.ker).trans (presentationKernelRelationsEquiv P))

/-- Native presentation coordinates evaluate its given generators. -/
@[simp] theorem presentedComplexPointsEquiv_apply (P : Algebra.Presentation ℂ S ι σ)
    (x : AffineComplexPoints.affineComplexPoints S) (i : ι) :
    (presentedComplexPointsEquiv P x).val i = x (P.val i) := by
  change x (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X i))) = _
  rw [P.quotientEquiv_mk, P.algebraMap_apply, MvPolynomial.aeval_X]

/-- Evaluating a polynomial in presentation coordinates evaluates its image in the algebra. -/
@[simp] theorem presentedComplexPointsEquiv_eval (P : Algebra.Presentation ℂ S ι σ)
    (x : AffineComplexPoints.affineComplexPoints S) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (presentedComplexPointsEquiv P x).val p =
      x (MvPolynomial.aeval P.val p) := by
  change MvPolynomial.eval
    (PresentationComplexPoints.presentationComplexPointsEquiv P.ker
      (x.comp (P.quotientEquiv.restrictScalars ℂ).toAlgHom)).val p = _
  rw [PresentationComplexPoints.presentationComplexPointsEquiv_eval]
  change x (P.quotientEquiv (Ideal.Quotient.mk P.ker p)) = _
  rw [P.quotientEquiv_mk, P.algebraMap_apply]

/-- The inverse evaluates any algebra element through the presentation's chosen representative. -/
@[simp] theorem presentedComplexPointsEquiv_symm_apply
    (P : Algebra.Presentation ℂ S ι σ)
    (z : {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0}) (s : S) :
    (presentedComplexPointsEquiv P).symm z s = MvPolynomial.eval z.val (P.σ s) := by
  simpa only [Equiv.apply_symm_apply, P.aeval_val_σ] using
    (presentedComplexPointsEquiv_eval P ((presentedComplexPointsEquiv P).symm z)
      (P.σ s)).symm

/-- Every algebra map is given in presentation coordinates by polynomial representatives. -/
theorem presentedComplexPointsEquiv_map_apply
    {T : Type u'} [CommRing T] [Algebra ℂ T] {κ : Type v'} {τ : Type w'}
    (P : Algebra.Presentation ℂ S ι σ) (Q : Algebra.Presentation ℂ T κ τ)
    (f : S →ₐ[ℂ] T) (x : AffineComplexPoints.affineComplexPoints T) (i : ι) :
    (presentedComplexPointsEquiv P (x.comp f)).val i =
      MvPolynomial.eval (presentedComplexPointsEquiv Q x).val
        (Q.σ (f (P.val i))) := by
  rw [presentedComplexPointsEquiv_apply, presentedComplexPointsEquiv_eval,
    Q.aeval_val_σ]
  rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.PresentedComplexPoints
