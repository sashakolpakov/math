import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Evaluation

/-! # Universal Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalMap.CrystallineFrameUniversalMap

noncomputable section

/-!
# The native crystalline map specified by lifted frame coordinates

Evaluation of the relative PD algebra respects the actual reduction maps
and yields a native crystalline morphism into the frame extension. Its
projection is the given morphism and its coordinates are the given lifts.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  {P Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}
  (f : P ⟶ Q) (y : σ → P.thickening.ring)
  (hy : ∀ i, P.thickening.reduction (y i) = AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B P (a i))

local notation "QR" => Q.thickening.ring
local notation "G" => DividedPowerAlgebra QR (σ →₀ QR)

theorem reduction_ambientMap (t : G) :
    P.thickening.reduction (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy t) =
      f.reducedMap (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening t) := by
  have he : P.thickening.reduction.comp (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy).toRingHom =
      f.reducedMap.toRingHom.comp (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening) := by
    apply FreeRelative.BaseChange.FreeRelativeBaseChange.ringHom_ext QR σ
    · intro x
      change P.thickening.reduction
        (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (algebraMap QR G x)) =
        f.reducedMap (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening (algebraMap QR G x))
      rw [Evaluation.CrystallineFrameEvaluation.ambientMap_coefficient, Map.CrystallineFrameMap.reduction_coefficient]
      exact f.reduction_comm x
    · intro n i
      change P.thickening.reduction (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ n i)) =
        f.reducedMap (PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ n i))
      by_cases hn : n = 0
      · subst n
        simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator, DividedPowerAlgebra.dp_zero, map_one]
      · have hQ := Map.CrystallineFrameMap.generator_mem Q n hn i
        have hP := (Evaluation.CrystallineFrameEvaluation.ambientMap_isDPMorphism p k B σ a f y hy).ideal_comp
          (Ideal.mem_map_of_mem (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy).toRingHom hQ)
        change PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ n i) = 0 at hQ
        change P.thickening.reduction (Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator QR σ n i)) = 0 at hP
        rw [hP, hQ]
        exact (map_zero f.reducedMap).symm
  exact RingHom.congr_fun he t

def map : P ⟶ (Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q where
  ambientMap := Evaluation.CrystallineFrameEvaluation.ambientMap p k B σ a f y hy
  reducedMap := f.reducedMap
  reduction_comm := reduction_ambientMap p k B σ a f y hy
  over_X := f.over_X
  dp_comp := Evaluation.CrystallineFrameEvaluation.ambientMap_isDPMorphism p k B σ a f y hy

theorem map_projection : map p k B σ a f y hy ≫ (Functor.CrystallineFrameFunctor.projection p k B σ a).app Q = f := by
  apply Site.Object.Hom.ext
  · rfl
  · apply AlgHom.ext
    intro x
    exact Evaluation.CrystallineFrameEvaluation.ambientMap_coefficient p k B σ a f y hy x

theorem map_coordinate (i : σ) :
    (map p k B σ a f y hy).ambientMap (Map.CrystallineFrameMap.coordinate a Q i) = y i :=
  Evaluation.CrystallineFrameEvaluation.ambientMap_coordinate p k B σ a f y hy i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalMap.CrystallineFrameUniversalMap
