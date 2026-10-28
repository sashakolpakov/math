import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.GradedEvaluation

/-! # Frobenius Form Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation

noncomputable section

/-! # The polynomial Frobenius evaluation square on coordinate differential symbols -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]
  [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ideal p k σ
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.dividedPowers p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)
local notation "IG" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal (R n) σ (I n)
local notation "γ" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (I n) (δ n)

def evaluationAlgebra (n : ℕ) : G n →ₐ[R n] R n where
  __ := FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n
  commutes' x := FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation_coefficient p k σ n x

def evaluation (n j : ℕ) : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j →+
    PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
  FreeRelative.GradedEvaluation.FreeRelativeGradedEvaluation.formMap W (R n) σ (I n) (δ n)
    (evaluationAlgebra p k σ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n) j

def ambient (n j : ℕ) : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j →+
    PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j :=
  (PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap (R n) (R n) (G n) (G n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.frobenius p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_coefficient p k σ n)
    (IG n) (γ n) (IG n) (γ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_isDPMorphism p k σ n) j).toAddMonoidHom

def power (n j : ℕ) : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j →+
    PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j :=
  ((PD.RelativeScalarSquare.PDRelativeScalarSquare.selfMap W (R n) (G n) (IG n) (γ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.power p k σ n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.power_isDPMorphism p k σ n)).f j).hom.toAddMonoidHom

omit [Fintype σ] [LinearOrder σ] in
theorem ambient_symbol (n j : ℕ) (b : G n) (v : Fin j → σ) :
    ambient p k σ n j
      (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v)) =
    PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient p k σ n b)
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v) := by
  let f := FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient p k σ n
  let t : σ → R n := BigCrystalline.FrameLifts.BigCrystallineFrameLifts.translation a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n)
  have hs := PD.DeRhamSemilinearMap.PDDeRhamSemilinearMap.formMap_symbol (R n) (R n) (G n) (G n)
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.frobenius p k σ n) f
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_coefficient p k σ n)
    (IG n) (γ n) (IG n) (γ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient_isDPMorphism p k σ n)
    j b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v)
  have hv : f ∘ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v) =
      (fun l => algebraMap (R n) (G n) (t (v l)) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 (v l)) :=
    funext (fun l => BigCrystalline.FrameMaps.BigCrystallineFrameMaps.ambientMap_coordinate a
      (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) (v l))
  exact hs.trans ((congrArg (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) (f b)) hv).trans
    (PD.FormTranslations.PDFormTranslations.add_base (R n) (G n) (IG n) (γ n) (f b)
      (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v) (t ∘ v)))

omit [PerfectRing k p] in
theorem evaluation_symbol (n j : ℕ) (b : G n) (v : Fin j → σ) :
    evaluation p k σ n j
      (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v)) =
    PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v) :=
  FreeRelative.GradedEvaluation.FreeRelativeGradedEvaluation.symbol W (R n) σ (I n) (δ n)
    (evaluationAlgebra p k σ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n) j b v

omit [PerfectRing k p] in
theorem power_symbol (n j : ℕ) (b : G n) (v : Fin j → σ) :
    evaluation p k σ n j (power p k σ n j
      (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v))) =
    PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.power p k σ n b))
      (fun l => FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n (v l) ^ p) :=
  FreeRelative.GradedEvaluation.FreeRelativeGradedEvaluation.power_symbol W (R n) σ (I n) (δ n)
    (evaluationAlgebra p k σ n) (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n) p
    (BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.targetLift a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))
    (BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.sourceLift a p (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))
    (BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.power_difference_mem a p (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n))
    (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation_coordinate p k σ n) j b v

theorem square_symbol (n j : ℕ) (b : G n) (v : Fin j → σ) :
    evaluation p k σ n j (power p k σ n j (ambient p k σ n j
      (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v)))) =
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j
      (evaluation p k σ n j
        (PD.DeRham.PDDeRham.symbol (R n) (G n) (IG n) (γ n) b (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 ∘ v))) := by
  let F : PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j → PD.DeRham.PDDeRham.Form W (R n) (I n) (δ n) j :=
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap p k σ n j
  have hs : F (PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v)) =
    PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n)
      (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b))
      (WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n ∘
        (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v)) :=
    WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.formsMap_symbol p k σ n j
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.evaluation p k σ n b)
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v)
  have hl := (congrArg (fun ω : PD.DeRham.PDDeRham.Form (R n) (G n) (IG n) (γ n) j =>
      evaluation p k σ n j (power p k σ n j ω)) (ambient_symbol p k σ n j b v)).trans
    (power_symbol p k σ n j (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ambient p k σ n b) v)
  have hr := (congrArg F (evaluation_symbol p k σ n j b v)).trans hs
  have hc := RingHom.congr_fun (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.square p k σ n) b
  have hv : WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n ∘
      (FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n ∘ v) =
      (fun l => FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.liftedCoordinate p k σ n (v l) ^ p) :=
    funext (fun l => FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.frobenius_coordinate p k σ n (v l))
  exact hl.trans ((congrArg₂ (PD.DeRham.PDDeRham.symbol W (R n) (I n) (δ n)) hc hv.symm).trans hr.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusFormEvaluation.BigPolynomialFrobeniusFormEvaluation
