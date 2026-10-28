import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Gaussian Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianLift.Weil

noncomputable section

/-! A continuous square root of the actual Gaussian determinant factor
selects a unique real metaplectic lift over a connected period family. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem realLift_eq_of_nonzero_action {r s : MpR}
    (hp : D.real.project r = D.real.project s)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz ι) (hf : f ≠ 0) (ha : D.real.action r f = D.real.action s f) : r = s := by
  have hk : D.real.project (r * s⁻¹) = 1 := by
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rcases (D.real.kernel _).mp hk with h | h
  · exact mul_inv_eq_one.mp h
  · have he : r = D.real.negOne * s := mul_inv_eq_iff_eq_mul.mp h
    rw [he, map_mul] at ha
    change D.real.action D.real.negOne (D.real.action s f) = D.real.action s f at ha
    rw [D.real.genuine] at ha
    have hz : (2 : ℂ) • D.real.action s f = 0 := by
      calc
        (2 : ℂ) • D.real.action s f = -D.real.action s f + D.real.action s f := by
          rw [two_smul]
          exact congrArg₂ (· + ·) ha.symm rfl
        _ = 0 := neg_add_cancel _
    have hz' : D.real.action s f = 0 :=
      (smul_eq_zero.mp hz).resolve_left (by norm_num)
    exact (hf ((D.real.action s).injective (hz'.trans (map_zero _).symm))).elim

theorem gaussianTest_ne_zero (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z ≠ 0 := by
  intro h
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz ι => f.val 0) h
  change RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z 0 = 0 at he
  rw [RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.gaussianFunction_zero] at he
  exact one_ne_zero he

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
  (Z : X → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (a : X → ℂ)

def HasGaussianFamilyAction (r : MpR) : Prop :=
  D.real.project r = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ ∧
    ∀ (x : X) (z : ι → ℂ),
      D.real.action r (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) z) =
        ((a x)⁻¹ * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Z x) z)⁻¹) •
          RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel (Z x))
            ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange (Z x) z)

theorem existsUnique_gaussianFamilyLift
    (hZ : Continuous (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) (ha : Continuous a)
    (hsq : ∀ x, a x ^ 2 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) :
    ∃! r : MpR, HasGaussianFamilyAction D Z γ a r := by
  have hc : Continuous (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Z x)) :=
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetDomain_continuous (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ)).comp hZ
  have hs : Set.EqOn (a ^ 2) ((fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (Z x)) ^ 2) Set.univ := by
    intro x _
    exact (hsq x).trans (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetDomain_sq (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))).symm
  have he := isPreconnected_univ.eq_or_eq_neg_of_sq_eq ha.continuousOn hc.continuousOn hs
    (fun _ => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)
  have hex : ∃ r : MpR, HasGaussianFamilyAction D Z γ a r := by
    rcases he with he | he
    · refine ⟨D.normalizedRealLift γ, D.normalizedRealLift_covers γ, fun x z => ?_⟩
      rw [he (Set.mem_univ x)]
      exact RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.realAction_gaussian D γ (Z x) z
    · refine ⟨D.real.negOne * D.normalizedRealLift γ, ?_, fun x z => ?_⟩
      · rw [map_mul, D.real.project_negOne, D.normalizedRealLift_covers, one_mul]
      · rw [map_mul]
        change D.real.action D.real.negOne
          (D.real.action (D.normalizedRealLift γ) (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) z)) = _
        rw [D.real.genuine, RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.realAction_gaussian, he (Set.mem_univ x)]
        simp only [Pi.neg_apply, inv_neg, neg_mul]
        exact (neg_smul _ _).symm
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, hr, fun s hs => ?_⟩
  let x := Classical.arbitrary X
  exact realLift_eq_of_nonzero_action D (hs.1.trans hr.1.symm)
    (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) 0) (gaussianTest_ne_zero D (Z x) 0)
    ((hs.2 x 0).trans (hr.2 x 0).symm)

def gaussianFamilyLift
    (hZ : Continuous (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) (ha : Continuous a)
    (hsq : ∀ x, a x ^ 2 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) : MpR :=
  (existsUnique_gaussianFamilyLift D Z γ a hZ ha hsq).choose

theorem gaussianFamilyLift_spec
    (hZ : Continuous (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) (ha : Continuous a)
    (hsq : ∀ x, a x ^ 2 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x))) :
    HasGaussianFamilyAction D Z γ a (gaussianFamilyLift D Z γ a hZ ha hsq) :=
  (existsUnique_gaussianFamilyLift D Z γ a hZ ha hsq).choose_spec.1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianLift.Weil
