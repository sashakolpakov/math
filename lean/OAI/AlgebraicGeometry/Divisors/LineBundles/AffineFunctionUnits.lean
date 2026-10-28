import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceProperCriterion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.RationalReciprocity
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.Unit

/-! # Affine Function Units -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineFunctionUnits.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: local residue reciprocity from actual separation of divisor components

Unit equations are handled by their zero Cartier cycles. For two
nonunits, separation of the actual minimal-prime supports proves the
maximal-radical parameter condition. This removes that extra parameter
hypothesis from proper regular and rational residue reciprocity.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [IsLocalRing R] [IsIntegrallyClosed R]

theorem affineDisjointResidueBoundary_zero (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hproper : ∀ P : Ideal R, P ∈ (Ideal.span {b}).minimalPrimes → a ∉ P) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0 := by
  by_cases hau : IsUnit a
  · exact Cartier.Unit.BundleCycles.normalResidueBoundaryCycle_globalUnit (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.Divisor.BundleCycles.affineAmbientSection R a) (hau.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) _ _ rfl
  by_cases hbu : IsUnit b
  · rw [ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_swap]
    have hz := Cartier.Unit.BundleCycles.normalResidueBoundaryCycle_globalUnit (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.Divisor.BundleCycles.affineAmbientSection R b) (hbu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) rfl
    rw [hz, neg_zero]
  exact Affine.ProperReciprocity.BundleCycles.affineProperResidueBoundary_zero R a b ha hb hdim
    (SurfaceProperCriterion.BundleCycles.surfaceProperPair_radical a b hb hdim hau hbu hproper)

theorem affineDisjointRationalResidueBoundary_zero (a c b d : R)
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hdim : ringKrullDim R = 2)
    (hab : ∀ P : Ideal R, P ∈ (Ideal.span {b}).minimalPrimes → a ∉ P)
    (had : ∀ P : Ideal R, P ∈ (Ideal.span {d}).minimalPrimes → a ∉ P)
    (hcb : ∀ P : Ideal R, P ∈ (Ideal.span {b}).minimalPrimes → c ∉ P)
    (hcd : ∀ P : Ideal R, P ∈ (Ideal.span {d}).minimalPrimes → c ∉ P) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha / Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R c hc)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb / Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R d hd) = 0 := by
  rw [Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_left, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    affineDisjointResidueBoundary_zero R a b ha hb hdim hab,
    affineDisjointResidueBoundary_zero R a d ha hd hdim had,
    affineDisjointResidueBoundary_zero R c b hc hb hdim hcb,
    affineDisjointResidueBoundary_zero R c d hc hd hdim hcd]
  simp only [sub_zero]

end

/-!
# LineBundleCycles: actual affine function units preserve products and quotients

The nonzero affine equation is sent through the actual global section
and generic-germ maps. These maps preserve multiplication, so the
residue-cycle bilinearity can be applied to genuine ring factorizations.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem affineFunctionUnit_mul (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R (a * b) (mul_ne_zero ha hb) = Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha * Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb := by
  apply Units.ext
  change RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Affine.Divisor.BundleCycles.affineAmbientSection R (a * b)) =
    RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Affine.Divisor.BundleCycles.affineAmbientSection R a) *
      RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Affine.Divisor.BundleCycles.affineAmbientSection R b)
  unfold RegularDivisor.BundleCycles.globalFunctionFieldElement Affine.Divisor.BundleCycles.affineAmbientSection
  rw [map_mul, map_mul]

omit [IsNoetherianRing R] in
theorem affineFunctionUnit_one : Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R 1 one_ne_zero = 1 := by
  apply Units.ext
  change RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Affine.Divisor.BundleCycles.affineAmbientSection R 1) = 1
  unfold RegularDivisor.BundleCycles.globalFunctionFieldElement Affine.Divisor.BundleCycles.affineAmbientSection
  rw [map_one, map_one]

theorem affineResidueBoundary_unit_left [IsIntegrallyClosed R]
    (a : R) (ha : IsUnit a) (h : (Spec (CommRingCat.of R)).functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha.ne_zero) h = 0 :=
  Cartier.Unit.BundleCycles.normalResidueBoundaryCycle_globalUnit (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
    (Affine.Divisor.BundleCycles.affineAmbientSection R a) (ha.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) _ _ rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineFunctionUnits.BundleCycles
