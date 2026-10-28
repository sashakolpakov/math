import OAI.AlgebraicGeometry.Foundations.Scheme.PresentedComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentationPointTopology

/-! # Presented Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentedPointTopology

noncomputable section

/-!
# Ordinary complex points in a native algebra presentation

A mathlib `Algebra.Presentation` supplies a proved quotient isomorphism to the
actual algebra. Combining it with the polynomial-presentation homeomorphism
identifies that algebra's complex points with the ordinary solution space of
the presentation's defining equations. The coordinates are the values of its
actual generators.
-/

universe u v w u' v' w'

variable {S : Type u} [CommRing S] [Algebra ℂ S]
variable {ι : Type v} {σ : Type w}

/-- The kernel and the specified presentation relations have the same subspace topology. -/
def presentationKernelRelationsHomeomorph (P : Algebra.Presentation ℂ S ι σ) :
    MvPolynomial.zeroLocus ℂ P.ker ≃ₜ
      {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0} where
  toEquiv := Foundations.Scheme.PresentedComplexPoints.presentationKernelRelationsEquiv P
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- A native presentation identifies the algebra's ordinary point space with its equations. -/
def presentedComplexPointsHomeomorph (P : Algebra.Presentation ℂ S ι σ) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints S ≃ₜ
      {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0} :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph (P.quotientEquiv.restrictScalars ℂ)).trans
    ((PresentationPointTopology.presentationComplexPointsHomeomorph P.ker).trans
      (presentationKernelRelationsHomeomorph P))

/-- The underlying bijection is the actual algebraic presentation correspondence. -/
@[simp]
theorem presentedComplexPointsHomeomorph_toEquiv (P : Algebra.Presentation ℂ S ι σ) :
    (presentedComplexPointsHomeomorph P).toEquiv = Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv P := rfl

/-- The ordinary coordinates evaluate the actual presentation generators. -/
@[simp]
theorem presentedComplexPointsHomeomorph_apply (P : Algebra.Presentation ℂ S ι σ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (i : ι) :
    (presentedComplexPointsHomeomorph P x).val i = x (P.val i) :=
  Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_apply P x i

/-- Polynomial coordinate evaluation recovers evaluation in the presented algebra. -/
@[simp]
theorem presentedComplexPointsHomeomorph_eval (P : Algebra.Presentation ℂ S ι σ)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (presentedComplexPointsHomeomorph P x).val p =
      x (MvPolynomial.aeval P.val p) :=
  Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_eval P x p

/-- The inverse homeomorphism evaluates representatives supplied by the presentation. -/
@[simp]
theorem presentedComplexPointsHomeomorph_symm_apply (P : Algebra.Presentation ℂ S ι σ)
    (z : {z : ι → ℂ // ∀ j, MvPolynomial.eval z (P.relation j) = 0}) (s : S) :
    (presentedComplexPointsHomeomorph P).symm z s = MvPolynomial.eval z.val (P.σ s) :=
  Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_symm_apply P z s

/-- Native presentation coordinates give a closed embedding of the actual point space. -/
theorem isClosedEmbedding_presentedCoordinates (P : Algebra.Presentation ℂ S ι σ) :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => fun i => x (P.val i)) := by
  have heq : (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => (presentedComplexPointsHomeomorph P x).val) =
      (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => fun i => x (P.val i)) := by
    funext x i
    exact presentedComplexPointsHomeomorph_apply P x i
  rw [← heq]
  exact (PresentationPointTopology.isClosed_equationsZeroLocus P.relation).isClosedEmbedding_subtypeVal.comp
    (presentedComplexPointsHomeomorph P).isClosedEmbedding

/-- Algebra maps have their actual polynomial coordinate expressions in these charts. -/
theorem presentedComplexPointsHomeomorph_map_apply
    {T : Type u'} [CommRing T] [Algebra ℂ T] {κ : Type v'} {τ : Type w'}
    (P : Algebra.Presentation ℂ S ι σ) (Q : Algebra.Presentation ℂ T κ τ)
    (f : S →ₐ[ℂ] T) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints T) (i : ι) :
    (presentedComplexPointsHomeomorph P (x.comp f)).val i =
      MvPolynomial.eval (presentedComplexPointsHomeomorph Q x).val
        (Q.σ (f (P.val i))) :=
  Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_map_apply P Q f x i

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PresentedPointTopology
