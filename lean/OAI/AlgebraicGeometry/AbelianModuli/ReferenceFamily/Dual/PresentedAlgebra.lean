import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.QuotientPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.PresentedComplexPoints

/-! # Presented Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra

noncomputable section

/-! The tangent-vector description transfers through an actual native
algebra presentation to dual-number points of that algebra. -/

open OAI.AlgebraicGeometry.Foundations.Scheme.PresentedComplexPoints

variable {S T : Type*} [CommRing S] [Algebra ℂ S] [CommRing T] [Algebra ℂ T]

def DualAlgebraPoints (x : S →ₐ[ℂ] ℂ) :=
  {f : S →ₐ[ℂ] DualNumber ℂ // (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f = x}

def dualAlgebraPointsEquiv (e : T ≃ₐ[ℂ] S) (x : S →ₐ[ℂ] ℂ) :
    DualAlgebraPoints (x.comp e.toAlgHom) ≃ DualAlgebraPoints x where
  toFun f := ⟨f.val.comp e.symm.toAlgHom, by
    apply AlgHom.ext
    intro s
    exact (DFunLike.congr_fun f.property (e.symm s)).trans (congrArg x (e.apply_symm_apply s))⟩
  invFun f := ⟨f.val.comp e.toAlgHom, by
    apply AlgHom.ext
    intro t
    exact DFunLike.congr_fun f.property (e t)⟩
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro t
    exact congrArg f.val (e.symm_apply_apply t)
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    exact congrArg f.val (e.apply_symm_apply s)

variable {ι σ : Type*} [Fintype ι]

omit [Fintype ι] in
theorem presentedDualPoint_coordinates (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) :
    QuotientPoints.quotientPointCoordinates P.ker (x.comp (P.quotientEquiv.restrictScalars ℂ).toAlgHom) =
      fun i => x (P.val i) := by
  funext i
  change x (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X i))) = x (P.val i)
  rw [P.quotientEquiv_mk, P.algebraMap_apply, MvPolynomial.aeval_X]

def presentedDualPointsEquiv (P : Algebra.Presentation ℂ S ι σ) (x : S →ₐ[ℂ] ℂ) :
    QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i)) ≃ DualAlgebraPoints x :=
  (Set.equivOfEq (congrArg (fun z => (QuotientPoints.polynomialRelationTangent P.ker z : Set (ι → ℂ)))
    (presentedDualPoint_coordinates P x).symm)).trans
      ((QuotientPoints.dualQuotientPointsEquiv P.ker (x.comp (P.quotientEquiv.restrictScalars ℂ).toAlgHom)).trans
        (dualAlgebraPointsEquiv (P.quotientEquiv.restrictScalars ℂ) x))

theorem presentedDualPointsEquiv_inverse (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (f : DualAlgebraPoints x) (i : ι) :
    ((presentedDualPointsEquiv P x).symm f).val i = (f.val (P.val i)).snd := by
  change (f.val (P.quotientEquiv (Ideal.Quotient.mk P.ker (MvPolynomial.X i)))).snd = _
  rw [P.quotientEquiv_mk, P.algebraMap_apply, MvPolynomial.aeval_X]

theorem presentedDualPointsEquiv_apply (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (v : QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i))) (i : ι) :
    ((presentedDualPointsEquiv P x v).val (P.val i)).snd = v.val i :=
  (presentedDualPointsEquiv_inverse P x (presentedDualPointsEquiv P x v) i).symm.trans
    (congrArg (fun w : QuotientPoints.polynomialRelationTangent P.ker (fun j => x (P.val j)) => w.val i)
      ((presentedDualPointsEquiv P x).symm_apply_apply v))

theorem presentedDualPointsEquiv_polynomial (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (v : QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i))) :
    PolynomialDifferential.dualPolynomialEvaluation (fun i => x (P.val i)) v.val =
      (presentedDualPointsEquiv P x v).val.comp (MvPolynomial.aeval P.val) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [PolynomialDifferential.dualPolynomialEvaluation_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
  apply TrivSqZeroExt.ext
  · exact (DFunLike.congr_fun (presentedDualPointsEquiv P x v).property (P.val i)).symm
  · exact (presentedDualPointsEquiv_apply P x v i).symm

theorem presentedDualPointsEquiv_eval (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (v : QuotientPoints.polynomialRelationTangent P.ker (fun i => x (P.val i))) (a : S) :
    ((presentedDualPointsEquiv P x v).val a).snd =
      fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y (P.σ a)) (fun i => x (P.val i)) v.val := by
  have h := DFunLike.congr_fun (presentedDualPointsEquiv_polynomial P x v) (P.σ a)
  change PolynomialDifferential.dualPolynomialEvaluation (fun i => x (P.val i)) v.val (P.σ a) =
    (presentedDualPointsEquiv P x v).val (MvPolynomial.aeval P.val (P.σ a)) at h
  rw [P.aeval_val_σ] at h
  exact (congrArg TrivSqZeroExt.snd h).symm.trans (PolynomialDifferential.dualPolynomialEvaluation_snd _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra
