import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.FrameFrobeniusCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerForms

/-! # Frobenius Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation

noncomputable section

/-! # The actual polynomial Frobenius square on evaluated big frame functions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "B" => MvPolynomial σ k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.AbsoluteFrobenius.PolynomialAbsoluteFrobenius.reduction p k σ
local notation "hr" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_surjective p k σ
local notation "hb" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Residue.WittPolynomialResidue.reduction_base p k σ
local notation "a" => fun i => r (MvPolynomial.X i)

abbrev ring (n : ℕ) := (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n).thickening.ring

abbrev ideal (n : ℕ) : Ideal (BigPolynomialFrobeniusEvaluation.ring p k σ n) :=
  RingHom.ker (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n).thickening.reduction

abbrev dividedPowers (n : ℕ) : DividedPowers (ideal p k σ n) :=
  (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n).thickening.dividedPowers

local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation.ring p k σ
local notation "G" => fun n => DividedPowerAlgebra (R n) (σ →₀ R n)

def coordinate (n : ℕ) (i : σ) : G n :=
  BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) i

def liftedCoordinate (n : ℕ) (i : σ) : R n :=
  (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).coordinate i

def evaluation (n : ℕ) : G n →+* R n :=
  BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation.map p k B σ a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
    (liftedCoordinate p k σ n)
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).reduction_coordinate

def ambient (n : ℕ) : G n →+* G n :=
  (BigCrystalline.FrameMaps.BigCrystallineFrameMaps.ambientMap a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n)).toRingHom

def power (n : ℕ) : G n →ₐ[R n] G n :=
  BigCrystalline.PowerForms.BigCrystallinePowerForms.ambientMap a p (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)

def frobenius (n : ℕ) : R n →+* R n := WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap p k σ n

omit [PerfectRing k p] in
theorem evaluation_coefficient (n : ℕ) (x : R n) :
    evaluation p k σ n (algebraMap (R n) (G n) x) = x :=
  BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation.coefficient p k B σ a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
    (liftedCoordinate p k σ n)
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).reduction_coordinate x

omit [PerfectRing k p] in
theorem evaluation_coordinate (n : ℕ) (i : σ) :
    evaluation p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i) = liftedCoordinate p k σ n i :=
  BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation.coordinate p k B σ a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
    (liftedCoordinate p k σ n)
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).reduction_coordinate i

theorem ambient_coefficient (n : ℕ) (x : R n) :
    ambient p k σ n (algebraMap (R n) (G n) x) =
      algebraMap (R n) (G n) (frobenius p k σ n x) :=
  BigCrystalline.FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) x

theorem power_ambient_coordinate (n : ℕ) (i : σ) :
    power p k σ n (ambient p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i)) = BigPolynomialFrobeniusEvaluation.coordinate p k σ n i ^ p := by
  have h₁ := BigCrystalline.FrameMaps.BigCrystallineFrameMaps.coordinate_naturality a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n) i
  have h₂ := FrobeniusLifts.BigPolynomialFrobeniusLifts.power_coordinate p k σ a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) i
  exact (congrArg (power p k σ n) h₁).trans h₂

theorem frobenius_coordinate (n : ℕ) (i : σ) :
    frobenius p k σ n (liftedCoordinate p k σ n i) = liftedCoordinate p k σ n i ^ p :=
  WittPolynomial.FrameFrobeniusCoordinates.WittPolynomialFrameFrobeniusCoordinates.coordinate p k σ n i

omit [PerfectRing k p] in
theorem evaluation_isDPMorphism (n : ℕ) : DividedPowers.IsDPMorphism
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n))
    (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n) (evaluation p k σ n) :=
  BigCrystalline.IntrinsicEvaluation.BigCrystallineIntrinsicEvaluation.isDPMorphism p k B σ a
    (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.nativeLevel p k σ n)
    (liftedCoordinate p k σ n)
    (FramedPolynomial.Levels.FramedPolynomialLevels.level p k B σ r hr hb n).reduction_coordinate

theorem ambient_isDPMorphism (n : ℕ) : DividedPowers.IsDPMorphism
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n))
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n))
    (ambient p k σ n) :=
  BigCrystalline.FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.morphism p k σ n)

omit [PerfectRing k p] in
theorem power_isDPMorphism (n : ℕ) : DividedPowers.IsDPMorphism
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n))
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers (R n) σ (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n))
    (power p k σ n).toRingHom :=
  BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates.map_isDPMorphism a p (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n)

theorem frobenius_isDPMorphism (n : ℕ) : DividedPowers.IsDPMorphism
    (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n) (frobenius p k σ n) :=
  WittPolynomial.FrameFrobenius.WittPolynomialFrameFrobenius.levelMap_isDPMorphism p k σ n

def geometric (n : ℕ) : G n →+* R n :=
  (evaluation p k σ n).comp ((power p k σ n).toRingHom.comp (ambient p k σ n))

def explicit (n : ℕ) : G n →+* R n := (frobenius p k σ n).comp (evaluation p k σ n)

theorem coefficient_square (n : ℕ) (x : R n) :
    geometric p k σ n (algebraMap (R n) (G n) x) =
      explicit p k σ n (algebraMap (R n) (G n) x) := by
  change evaluation p k σ n (power p k σ n (ambient p k σ n (algebraMap (R n) (G n) x))) =
    frobenius p k σ n (evaluation p k σ n (algebraMap (R n) (G n) x))
  rw [ambient_coefficient, AlgHom.commutes, evaluation_coefficient, evaluation_coefficient]

theorem coordinate_square (n : ℕ) (i : σ) :
    geometric p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i) = explicit p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i) := by
  change evaluation p k σ n (power p k σ n (ambient p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i))) =
    frobenius p k σ n (evaluation p k σ n (BigPolynomialFrobeniusEvaluation.coordinate p k σ n i))
  rw [power_ambient_coordinate, map_pow, evaluation_coordinate, frobenius_coordinate]

theorem square (n : ℕ) : geometric p k σ n = explicit p k σ n := by
  apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate (R n) σ
    (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n) (R n) (ideal p k σ n) (BigPolynomialFrobeniusEvaluation.dividedPowers p k σ n)
  · exact (evaluation_isDPMorphism p k σ n).comp _
      ((power_isDPMorphism p k σ n).comp _ (ambient_isDPMorphism p k σ n))
  · exact (frobenius_isDPMorphism p k σ n).comp _ (evaluation_isDPMorphism p k σ n)
  · exact coefficient_square p k σ n
  · intro i
    have hx := coordinate_square p k σ n i
    let c : R n := BigCrystalline.FrameLifts.BigCrystallineFrameLifts.lift p W B σ (Ideal.span {(p : W)})
        (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k
          (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) a
        (FrobeniusMorphism.BigPolynomialFrobeniusMorphism.level p k σ n) i
    have hc := coefficient_square p k σ n c
    change geometric p k σ n (algebraMap (R n) (G n) c + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 i) =
      explicit p k σ n (algebraMap (R n) (G n) c + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator (R n) σ 1 i) at hx
    rw [map_add, map_add, hc] at hx
    exact add_left_cancel hx

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigPolynomial.FrobeniusEvaluation.BigPolynomialFrobeniusEvaluation
