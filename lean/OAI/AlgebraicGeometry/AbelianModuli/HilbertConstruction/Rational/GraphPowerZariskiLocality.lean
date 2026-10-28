import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveGlobalDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor

/-! # Graph Power Zariski Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GraphPowerZariskiLocality

noncomputable section

/-! The original normalized graph-power polarization predicate is
Zariski-local on all test schemes. The fixed dual and its covering
isogeny are constructed from the projective family over the rational
Noetherian base; they are not extra hypotheses on the moduli problem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme.{0}} (M : Over B) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (qS : M.left ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

include P qS hd hδ in
theorem rationalNormalizedGraphPower_zariskiLocalMembership :
    SubfunctorOpen.SubfunctorZariskiLocalMembership
      (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d) := by
  let G := GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d
  let D := ProjectiveGlobalDual.RationalProjectiveGlobalDual.dualData F.abelian P qS
  let m := ProjectiveGlobalDual.RationalProjectiveGlobalDual.inducingIsogeny F.abelian P qS
  intro T y hy
  let V : Over M.left := Over.mk y.left
  let R₀ := G.sieveOfSection y
  let R : Sieve V := (Sieve.overEquiv V).symm (Sieve.overEquiv T R₀)
  have hR : R ∈ (Scheme.zariskiTopology.over M.left) V := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv V ((Sieve.overEquiv V).symm (Sieve.overEquiv T R₀)) ∈
      Scheme.zariskiTopology T.left
    rw [OrderIso.apply_symm_apply]
    exact (GrothendieckTopology.mem_over_iff Scheme.zariskiTopology R₀).mp hy
  have hlocal {U : Over M.left} (c : U ⟶ V) (hc : R c) :
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback U.hom)
        ((F.abelian.zeroNormalizedBundle L).pullback
          (pullback.fst F.abelian.scheme.hom U.hom)) d) := by
    have hc₀ : Sieve.overEquiv T R₀ c.left :=
      (Sieve.overEquiv_symm_iff (X := M.left) (Y := V) (Z := U)
        (Sieve.overEquiv T R₀) c).mp hc
    have hc₁ : R₀ (Over.homMk c.left : Over.mk (c.left ≫ T.hom) ⟶ T) :=
      (Sieve.overEquiv_iff R₀ c.left).mp hc₀
    change Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback (c.left ≫ y.left))
      ((F.abelian.zeroNormalizedBundle L).pullback
        (pullback.fst F.abelian.scheme.hom (c.left ≫ y.left))) d) at hc₁
    have hw : c.left ≫ y.left = U.hom := c.w
    exact hw ▸ hc₁
  exact Fixed.DualGraphPowerDescent.zeroNormalizedGraphPowerEnhancement_of_cover F.abelian P D m F.level
    L d hd hδ V R hR hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GraphPowerZariskiLocality
