import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PolynomialDifferential
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.QuotientPoints

noncomputable section

section

/-! Dual-number points of an actual affine polynomial quotient are
exactly the vectors annihilated by the analytic derivatives of its
defining ideal. -/

variable {ι : Type*} [Fintype ι]

def quotientPointCoordinates (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) : ι → ℂ :=
  fun i => x (Ideal.Quotient.mk I (MvPolynomial.X i))

omit [Fintype ι] in
theorem quotientPointCoordinates_eval (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) :
    MvPolynomial.aeval (quotientPointCoordinates I x) = x.comp (Ideal.Quotient.mkₐ ℂ I) := by
  apply MvPolynomial.algHom_ext
  intro i
  exact MvPolynomial.aeval_X _ i

omit [Fintype ι] in
theorem quotientPointCoordinates_relation (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) (p : MvPolynomial ι ℂ) (hp : p ∈ I) :
    MvPolynomial.eval (quotientPointCoordinates I x) p = 0 :=
  (DFunLike.congr_fun (quotientPointCoordinates_eval I x) p).trans
    ((congrArg x (Ideal.Quotient.eq_zero_iff_mem.mpr hp)).trans x.map_zero)

def polynomialRelationTangent (I : Ideal (MvPolynomial ι ℂ)) (x : ι → ℂ) : Submodule ℂ (ι → ℂ) :=
  ⨅ p : I, LinearMap.ker (fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p.val) x).toLinearMap

omit [Fintype ι] in
theorem mem_polynomialRelationTangent (I : Ideal (MvPolynomial ι ℂ)) (x v : ι → ℂ) :
    v ∈ polynomialRelationTangent I x ↔
      ∀ p : MvPolynomial ι ℂ, p ∈ I → fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v = 0 := by
  simp only [polynomialRelationTangent, Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h p hp => h ⟨p, hp⟩, fun h p => h p.val p.property⟩

def DualQuotientPoints (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) :=
  {f : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] DualNumber ℂ // (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f = x}

def dualQuotientPoint (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ)
    (v : polynomialRelationTangent I (quotientPointCoordinates I x)) : DualQuotientPoints I x := by
  let f := PolynomialDifferential.dualPolynomialEvaluation (quotientPointCoordinates I x) v.val
  have hf (p : MvPolynomial ι ℂ) (hp : p ∈ I) : f p = 0 :=
    (PolynomialDifferential.dualPolynomialEvaluation_eq_zero_iff _ _ p).mpr
      ⟨quotientPointCoordinates_relation I x p hp,
        (mem_polynomialRelationTangent I _ v.val).mp v.property p hp⟩
  refine ⟨Ideal.Quotient.liftₐ I f hf, ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro p
  change (f p).fst = x (Ideal.Quotient.mk I p)
  exact (PolynomialDifferential.dualPolynomialEvaluation_fst _ _ p).trans
    (DFunLike.congr_fun (quotientPointCoordinates_eval I x) p)

def dualQuotientCoordinates (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) (f : DualQuotientPoints I x) : ι → ℂ :=
  fun i => (f.val (Ideal.Quotient.mk I (MvPolynomial.X i))).snd

omit [Fintype ι] in
theorem dualQuotientCoordinates_polynomial (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) (f : DualQuotientPoints I x) :
    PolynomialDifferential.dualPolynomialEvaluation (quotientPointCoordinates I x) (dualQuotientCoordinates I x f) =
      f.val.comp (Ideal.Quotient.mkₐ ℂ I) := by
  let g : PolynomialDifferential.DualPolynomialPoints (quotientPointCoordinates I x) :=
    ⟨f.val.comp (Ideal.Quotient.mkₐ ℂ I), by
      exact (AlgHom.comp_assoc _ _ _).symm.trans
        ((congrArg (fun h => h.comp (Ideal.Quotient.mkₐ ℂ I)) f.property).trans
          (quotientPointCoordinates_eval I x).symm)⟩
  exact PolynomialDifferential.dualPolynomialPoint_coordinates _ g

theorem dualQuotientCoordinates_mem (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) (f : DualQuotientPoints I x) :
    dualQuotientCoordinates I x f ∈ polynomialRelationTangent I (quotientPointCoordinates I x) := by
  apply (mem_polynomialRelationTangent I _ _).mpr
  intro p hp
  have h : PolynomialDifferential.dualPolynomialEvaluation (quotientPointCoordinates I x) (dualQuotientCoordinates I x f) p = 0 :=
    (DFunLike.congr_fun (dualQuotientCoordinates_polynomial I x f) p).trans
      ((congrArg f.val (Ideal.Quotient.eq_zero_iff_mem.mpr hp)).trans f.val.map_zero)
  exact (PolynomialDifferential.dualPolynomialEvaluation_eq_zero_iff _ _ p).mp h |>.2

def dualQuotientPointsEquiv (I : Ideal (MvPolynomial ι ℂ))
    (x : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ) :
    polynomialRelationTangent I (quotientPointCoordinates I x) ≃ DualQuotientPoints I x where
  toFun := dualQuotientPoint I x
  invFun f := ⟨dualQuotientCoordinates I x f, dualQuotientCoordinates_mem I x f⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact congrArg TrivSqZeroExt.snd (PolynomialDifferential.dualPolynomialEvaluation_X (quotientPointCoordinates I x) v.val i)
  right_inv f := by
    apply Subtype.ext
    apply Ideal.Quotient.algHom_ext
    exact dualQuotientCoordinates_polynomial I x f

end

/-! Tangency to the defining ideal is equivalent to the actual
linearized generating equations. This is proved through evaluation in
the dual-number ring, so all products of ideal generators are handled. -/

variable {ι σ : Type*} [Fintype ι]

theorem mem_polynomialRelationTangent_span (F : σ → MvPolynomial ι ℂ)
    (x v : ι → ℂ) (hx : ∀ j, MvPolynomial.eval x (F j) = 0) :
    v ∈ polynomialRelationTangent (Ideal.span (Set.range F)) x ↔
      ∀ j, fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y (F j)) x v = 0 := by
  constructor
  · intro h j
    exact (mem_polynomialRelationTangent _ x v).mp h (F j) (Ideal.subset_span ⟨j, rfl⟩)
  · intro h
    have hker : Ideal.span (Set.range F) ≤ RingHom.ker (PolynomialDifferential.dualPolynomialEvaluation x v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact (PolynomialDifferential.dualPolynomialEvaluation_eq_zero_iff x v (F j)).mpr ⟨hx j, h j⟩
    apply (mem_polynomialRelationTangent _ x v).mpr
    intro p hp
    exact ((PolynomialDifferential.dualPolynomialEvaluation_eq_zero_iff x v p).mp (hker hp)).2

def polynomialJacobianMap [Fintype σ] (F : σ → MvPolynomial ι ℂ)
    (x : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi (fun j => (fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y (F j)) x).toLinearMap)

theorem polynomialRelationTangent_eq_kernel [Fintype σ] (F : σ → MvPolynomial ι ℂ)
    (x : ι → ℂ) (hx : ∀ j, MvPolynomial.eval x (F j) = 0) :
    polynomialRelationTangent (Ideal.span (Set.range F)) x = (polynomialJacobianMap F x).ker := by
  ext v
  rw [mem_polynomialRelationTangent_span F x v hx]
  change (∀ j, fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y (F j)) x v = 0) ↔
    polynomialJacobianMap F x v = 0
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.QuotientPoints
