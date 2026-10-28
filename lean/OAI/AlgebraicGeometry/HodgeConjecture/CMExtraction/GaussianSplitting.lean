import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Complement

/-! # Gaussian Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianSplitting.Weil

noncomputable section

/-! A determinant square-root cocycle on a connected period family gives
actual compatible real and finite group homomorphisms in PoissonAutomorphy's cover. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA G X : Type*} [Group MpR] [Group MpF] [Group MpA] [Group G]
  [TopologicalSpace X] [ConnectedSpace X] [MulAction G X]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (σ : G →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ)
  (Z : X → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (a : G → X → ℂ)
  (hZ : Continuous (fun x => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x)))
  (ha : ∀ g, Continuous (a g))
  (hsq : ∀ g x, a g x ^ 2 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (σ g)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (Z x)))
  (hperiod : ∀ g x, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (σ g)).transformSiegel (Z x) = Z (g • x))

def familyRealElement (g : G) : MpR :=
  GaussianLift.Weil.gaussianFamilyLift D Z (σ g) (a g) hZ (ha g) (hsq g)

omit [MulAction G X] in
theorem familyRealElement_covers (g : G) :
    D.real.project (familyRealElement D σ Z a hZ ha hsq g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) (σ g) :=
  (GaussianLift.Weil.gaussianFamilyLift_spec D Z (σ g) (a g) hZ (ha g) (hsq g)).1

include hperiod in
theorem familyRealElement_gaussian_zero (g : G) (x : X) :
    D.real.action (familyRealElement D σ Z a hZ ha hsq g) (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) 0) =
      (a g x)⁻¹ • RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z (g • x)) 0 := by
  have h := (GaussianLift.Weil.gaussianFamilyLift_spec D Z (σ g) (a g) hZ (ha g) (hsq g)).2 x 0
  simpa only [familyRealElement, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor_zero, inv_one, mul_one, map_zero, hperiod] using h

variable (hone : ∀ x, a 1 x = 1)
  (hmul : ∀ g h x, a (g * h) x = a g (h • x) * a h x)

include hperiod hone hmul in
def familyRealSplitting : G →* MpR where
  toFun := familyRealElement D σ Z a hZ ha hsq
  map_one' := by
    let x := Classical.arbitrary X
    refine GaussianLift.Weil.realLift_eq_of_nonzero_action D ?_ (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) 0)
      (GaussianLift.Weil.gaussianTest_ne_zero D (Z x) 0) ?_
    · rw [familyRealElement_covers, map_one, map_one, map_one]
    · rw [familyRealElement_gaussian_zero D σ Z a hZ ha hsq hperiod, hone]
      simp
  map_mul' g h := by
    let x := Classical.arbitrary X
    refine GaussianLift.Weil.realLift_eq_of_nonzero_action D ?_ (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (Z x) 0)
      (GaussianLift.Weil.gaussianTest_ne_zero D (Z x) 0) ?_
    · simp only [map_mul, familyRealElement_covers]
    · rw [map_mul]
      change D.real.action (familyRealElement D σ Z a hZ ha hsq (g * h)) _ =
        D.real.action (familyRealElement D σ Z a hZ ha hsq g)
          (D.real.action (familyRealElement D σ Z a hZ ha hsq h) _)
      rw [familyRealElement_gaussian_zero D σ Z a hZ ha hsq hperiod,
        familyRealElement_gaussian_zero D σ Z a hZ ha hsq hperiod, map_smul,
        familyRealElement_gaussian_zero D σ Z a hZ ha hsq hperiod, smul_smul,
        hmul, mul_inv_rev]
      rw [mul_smul g h x]

theorem familyRealSplitting_covers (g : G) :
    D.real.project (familyRealSplitting D σ Z a hZ ha hsq hperiod hone hmul g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) (σ g) :=
  familyRealElement_covers D σ Z a hZ ha hsq g

def familyFiniteSplitting : G →* MpF :=
  Finite.Complement.Weil.finiteComplement D σ (familyRealSplitting D σ Z a hZ ha hsq hperiod hone hmul)
    (familyRealSplitting_covers D σ Z a hZ ha hsq hperiod hone hmul)

theorem familySplitting_factorization (g : G) :
    D.includeReal (familyRealSplitting D σ Z a hZ ha hsq hperiod hone hmul g) *
      D.includeFinite (familyFiniteSplitting D σ Z a hZ ha hsq hperiod hone hmul g) =
        D.rationalSplit (σ g) :=
  Finite.Complement.Weil.finiteComplement_factorization D σ _ _ g

theorem familyFiniteSplitting_covers (g : G) :
    D.finite.project (familyFiniteSplitting D σ Z a hZ ha hsq hperiod hone hmul g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (σ g) :=
  Finite.Complement.Weil.finiteComplement_covers D σ _ _ g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianSplitting.Weil
