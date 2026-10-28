import OAI.RepresentationTheory.Theta.Geometric.Descent
import OAI.RepresentationTheory.Theta.Geometric.AdelicEq

/-! # Branch Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric.BranchTrace

noncomputable section

/-!
The active branch sum is built from Arithmetic representatives and actual cotangent
pullbacks. Its equality with the finite Weil coset sum is proved using the
canonical theta map. No branch-covariance or theta-identification field is
introduced. Relating this analytic trace to the algebraic PEL trace remains
the separate geometric realization obligation.
-/

variable {GQ Gq Ga : Type*} [Group GQ]
  [Group Gq] [TopologicalSpace Gq] [IsTopologicalGroup Gq]
  [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
  [MulAction GQ LinearTheta.BallCoordinates]

def activeRationalRepresentative (qf : GQ →* Gq × Ga)
    (h_Arithmetic : DenseRange qf) (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (c : Gq ⧸ Kq.toSubgroup) : GQ :=
  Classical.choose (No.rational_representative_of_Arithmetic qf h_Arithmetic Kq Ka c.out⁻¹)

omit [MulAction GQ LinearTheta.BallCoordinates] in
theorem activeRationalRepresentative_mem (qf : GQ →* Gq × Ga)
    (h_Arithmetic : DenseRange qf) (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (c : Gq ⧸ Kq.toSubgroup) :
    qf (activeRationalRepresentative qf h_Arithmetic Kq Ka c) * (c.out, 1) ∈
      Kq.toSubgroup.prod Ka.toSubgroup := by
  have h := Classical.choose_spec
    (No.rational_representative_of_Arithmetic qf h_Arithmetic Kq Ka c.out⁻¹)
  exact ⟨by simpa [activeRationalRepresentative] using h.1,
    by simpa [activeRationalRepresentative] using h.2⟩

theorem activeRationalRepresentative_branch (qf : GQ →* Gq × Ga)
    (h_Arithmetic : DenseRange qf) (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (c : Gq ⧸ Kq.toSubgroup) (L : LinearTheta.BallCoordinates) :
    AdelicEq.Adelic.point qf (Kq.toSubgroup.prod Ka.toSubgroup) L (c.out, 1) =
      AdelicEq.Adelic.point qf (Kq.toSubgroup.prod Ka.toSubgroup)
        (activeRationalRepresentative qf h_Arithmetic Kq Ka c • L) 1 := by
  simpa using AdelicEq.Adelic.branch_eq_rational_period qf
    (Kq.toSubgroup.prod Ka.toSubgroup) (c.out, 1)⁻¹
    (activeRationalRepresentative qf h_Arithmetic Kq Ka c)
    (by simpa using activeRationalRepresentative_mem qf h_Arithmetic Kq Ka c) L

/-- The branch trace on the ball cover is a finite sum of genuine
cotangent pullbacks, weighted by the spherical operator's identity column. -/
def activeBranchTrace (qf : GQ →* Gq × Ga) (h_Arithmetic : DenseRange qf)
    (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (T : SphericalGU.Spherical.algebra Kq.toSubgroup) :
    (D → LinearTheta.Cotangent) →ₗ[ℂ] (D → LinearTheta.Cotangent) :=
  (SphericalGU.Spherical.kernel Kq.toSubgroup T).sum fun c a =>
    (a : ℂ) • Descent.cotangentPullback D hpreserves
      (activeRationalRepresentative qf h_Arithmetic Kq Ka c)

variable {ι : Type*} [Fintype ι]

omit [MulAction GQ LinearTheta.BallCoordinates] in
/-- The inverse finite action of an Arithmetic representative equals the active
coset action on a product-level fixed input. This removes the away factor
using its actual stabilizer condition. -/
theorem representative_inverse_weil (qf : GQ →* Gq × Ga)
    (h_Arithmetic : DenseRange qf) (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (rho : Gq × Ga →* (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι))
    (φ : SphericalGU.Spherical.fixedInputs (Kq.toSubgroup.prod Ka.toSubgroup) rho)
    (c : Gq ⧸ Kq.toSubgroup) :
    rho (qf (activeRationalRepresentative qf h_Arithmetic Kq Ka c))⁻¹ φ.val =
      rho (c.out, 1) φ.val := by
  apply SphericalGU.Spherical.weil_value_eq_of_same_coset _ rho φ
  apply QuotientGroup.eq.mpr
  simpa only [inv_inv] using
    activeRationalRepresentative_mem qf h_Arithmetic Kq Ka c

/-- Rational covariance from ThetaOneForms and Arithmetic imply covariance of the
constructed analytic trace for the actual PoissonAutomorphy/DerivativeFactorization theta one-form. -/
theorem canonical_active_branch_trace
    (qf : GQ →* Gq × Ga) (h_Arithmetic : DenseRange qf)
    (Kq : OpenSubgroup Gq) (Ka : OpenSubgroup Ga)
    (D : Set LinearTheta.BallCoordinates)
    (hpreserves : ∀ γ : GQ, ∀ x ∈ D, γ • x ∈ D)
    (period : LinearTheta.BallCoordinates → AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (project : LinearTheta.BallCoordinates → ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] LinearTheta.Cotangent)
    (rho : Gq × Ga →* (PoissonAutomorphyNormalizationData.finiteSchwartz ι ≃ₗ[ℂ] PoissonAutomorphyNormalizationData.finiteSchwartz ι))
    (h_ThetaOneForms : ∀ γ φ,
      Descent.cotangentPullback D hpreserves γ
        (Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project (rho (qf γ) φ))) =
        Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project φ))
    (T : SphericalGU.Spherical.algebra Kq.toSubgroup)
    (φ : SphericalGU.Spherical.fixedInputs (Kq.toSubgroup.prod Ka.toSubgroup) rho) :
    activeBranchTrace qf h_Arithmetic Kq Ka D hpreserves T
        (Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project φ.val)) =
      Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project
        (SphericalGU.Spherical.weilOperator Kq.toSubgroup
          (rho.comp (MonoidHom.inl Gq Ga)) T φ.val)) := by
  have hcov (γ : GQ) :
      Descent.cotangentPullback D hpreserves γ
        (Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project φ.val)) =
      Descent.restrictForm D (LinearTheta.thetaOneFormLinear period project (rho (qf γ)⁻¹ φ.val)) := by
    simpa [← LinearEquiv.mul_apply, ← map_mul] using
      h_ThetaOneForms γ (rho (qf γ)⁻¹ φ.val)
  simp only [activeBranchTrace, SphericalGU.Spherical.weilOperator, LinearMap.finsupp_sum_apply,
    LinearMap.smul_apply, hcov, representative_inverse_weil]
  simp only [Finsupp.sum, map_sum, map_smul, LinearEquiv.coe_coe,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.BranchTrace
