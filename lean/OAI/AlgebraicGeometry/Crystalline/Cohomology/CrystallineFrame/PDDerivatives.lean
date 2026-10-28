import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators

/-! # PD Derivatives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PDDerivatives.CrystallineFramePDDerivatives

noncomputable section

/-! # The native frame differential is a PD coordinate derivative -/

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))

local notation "W" => WittVector p k
local notation "G" => CategoryTheory.Functor.obj (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a) Q

def derivation (i : σ) : Derivation W (G).thickening.ring (G).thickening.ring :=
  (FreeDivided.Derivation.FreeDividedDerivation.derivation Q.thickening.ring σ i).restrictScalars W

theorem dpow (i : σ) (m : ℕ) (x : (G).thickening.ring)
    (hx : x ∈ RingHom.ker (G).thickening.reduction) :
    derivation p k B σ a Q i ((G).thickening.dividedPowers.dpow (m + 1) x) =
      (G).thickening.dividedPowers.dpow m x * derivation p k B σ a Q i x := by
  have hx' : x ∈ Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.thickening.ring σ
      (RingHom.ker Q.thickening.reduction) :=
    PolynomialThickening.CrystallinePolynomialThickening.reduction_kernel p k Q.residueRing σ Q.thickening ▸ hx
  exact Divided.AffineMaps.DividedAffineMaps.derivation_dpow Q.thickening.ring σ
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers i m x hx'

theorem coordinate (i j : σ) [Decidable (j = i)] :
    derivation p k B σ a Q i (Map.CrystallineFrameMap.coordinate a Q j) =
      if j = i then 1 else 0 := by
  change FreeDivided.Derivation.FreeDividedDerivation.derivation Q.thickening.ring σ i
    (algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
      (Lifts.CrystallineFrameLifts.lift p k B σ a Q j) +
        Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 j) = _
  rw [map_add, Derivation.map_algebraMap, zero_add, FreeDivided.Derivation.FreeDividedDerivation.derivation_coordinate]
  rfl

theorem operator_eq (i : σ) :
    ((Operators.CrystallineFrameOperators.derivative p k B σ a i).app (Opposite.op Q)).hom =
      (derivation p k B σ a Q i).toLinearMap := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PDDerivatives.CrystallineFramePDDerivatives
