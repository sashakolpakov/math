import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Map

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor

noncomputable section

/-!
# Functorial crystalline polynomial frame extensions

Affine coordinate changes compose by the cocycle identity for lift
discrepancies. The resulting native endofunctor has a natural projection
and a compatible map from the fixed polynomial frame into ambient functions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Map.CrystallineFrameMap OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B

variable {p k B σ}
variable {Q P U : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)}

theorem map_id (Q : Site.Object p k X) : Map.CrystallineFrameMap.map a (𝟙 Q) = 𝟙 (Map.CrystallineFrameMap.object p k B σ Q) := by
  apply Site.Object.Hom.ext
  · rfl
  · have he : (Map.CrystallineFrameMap.ambientMap a (𝟙 Q)).toRingHom =
        RingHom.id (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring)) := by
      apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate Q.thickening.ring σ
        (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
        (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
        (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.thickening.ring σ (RingHom.ker Q.thickening.reduction))
        (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
          (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
        _ _ (Map.CrystallineFrameMap.ambientMap_relativePD a (𝟙 Q)) ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
      · intro t
        exact Map.CrystallineFrameMap.ambientMap_coefficient a (𝟙 Q) t
      · intro i
        change Map.CrystallineFrameMap.ambientMap a (𝟙 Q) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i
        rw [Map.CrystallineFrameMap.ambientMap_coordinate, Lifts.CrystallineFrameLifts.translation_id, map_zero, zero_add]
    exact AlgHom.ext (RingHom.congr_fun he)

theorem map_comp (f : Q ⟶ P) (g : P ⟶ U) : Map.CrystallineFrameMap.map a (f ≫ g) = Map.CrystallineFrameMap.map a f ≫ Map.CrystallineFrameMap.map a g := by
  apply Site.Object.Hom.ext
  · rfl
  · have he : (Map.CrystallineFrameMap.map a (f ≫ g)).ambientMap.toRingHom = (Map.CrystallineFrameMap.map a f ≫ Map.CrystallineFrameMap.map a g).ambientMap.toRingHom := by
      apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate U.thickening.ring σ
        (RingHom.ker U.thickening.reduction) U.thickening.dividedPowers
        (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
        (Multivariable.DividedPowers.MultivariableDividedPowers.ideal Q.thickening.ring σ (RingHom.ker Q.thickening.reduction))
        (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.thickening.ring σ
          (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers)
        _ _ (Map.CrystallineFrameMap.ambientMap_relativePD a (f ≫ g))
        ((Map.CrystallineFrameMap.ambientMap_relativePD a f).comp _ (Map.CrystallineFrameMap.ambientMap_relativePD a g))
      · intro t
        exact (Map.CrystallineFrameMap.ambientMap_coefficient a (f ≫ g) t).trans
          ((congrArg (Map.CrystallineFrameMap.ambientMap a f) (Map.CrystallineFrameMap.ambientMap_coefficient a g t)).trans
            (Map.CrystallineFrameMap.ambientMap_coefficient a f (g.ambientMap t))).symm
      · intro i
        change Map.CrystallineFrameMap.ambientMap a (f ≫ g) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.thickening.ring σ 1 i) =
          Map.CrystallineFrameMap.ambientMap a f (Map.CrystallineFrameMap.ambientMap a g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator U.thickening.ring σ 1 i))
        rw [Map.CrystallineFrameMap.ambientMap_coordinate, Map.CrystallineFrameMap.ambientMap_coordinate, map_add, Map.CrystallineFrameMap.ambientMap_coefficient,
          Map.CrystallineFrameMap.ambientMap_coordinate, Lifts.CrystallineFrameLifts.translation_comp, map_add]
        ac_rfl
    exact AlgHom.ext (RingHom.congr_fun he)

variable (p k B σ)

/-- The actual native frame extension with its affine transition maps. -/
def functor : Site.Object p k X ⥤ Site.Object p k X where
  obj := Map.CrystallineFrameMap.object p k B σ
  map := Map.CrystallineFrameMap.map a
  map_id := CrystallineFrameFunctor.map_id a
  map_comp := CrystallineFrameFunctor.map_comp a

def projection : functor p k B σ a ⟶ 𝟭 (Site.Object p k X) where
  app Q := (PolynomialFunctor.CrystallinePolynomialFunctor.projection p k X σ).app Q
  naturality {Q P} f := by
    apply Site.Object.Hom.ext
    · ext; rfl
    · ext t
      exact Map.CrystallineFrameMap.ambientMap_coefficient a f t

variable {p k B σ}

def polynomialMap (Q : Site.Object p k X) :
    MvPolynomial σ W →ₐ[W] DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring) :=
  MvPolynomial.aeval (Map.CrystallineFrameMap.coordinate a Q)

theorem polynomialMap_naturality (f : Q ⟶ P) :
    (Map.CrystallineFrameMap.ambientMap a f).comp (polynomialMap a P) = polynomialMap a Q := by
  apply MvPolynomial.algHom_ext
  intro i
  change Map.CrystallineFrameMap.ambientMap a f (MvPolynomial.aeval (Map.CrystallineFrameMap.coordinate a P) (MvPolynomial.X i)) =
    MvPolynomial.aeval (Map.CrystallineFrameMap.coordinate a Q) (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, Map.CrystallineFrameMap.coordinate_naturality]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Functor.CrystallineFrameFunctor
