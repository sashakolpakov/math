import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor

/-! # Dual Graph Power Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerLocality

noncomputable section

/-! A fixed actual dual and a covering isogeny give Zariski membership
descent for the original normalized graph-power subfunctor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme} (M : Over B) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (L : Line.Bundles.LineBundle F.abelian.scheme.left) (D : Dual.Data.DualAbelianData F.abelian)
    (m : Abelian.Schemes.AbelianScheme.Isogeny F.abelian D.abelian)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

include P D m hd hδ in
theorem fixedDualNormalizedGraphPower_zariskiLocalMembership :
    SubfunctorOpen.SubfunctorZariskiLocalMembership
      (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d) := by
  let G := GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle L) d
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
  exact DualGraphPowerDescent.zeroNormalizedGraphPowerEnhancement_of_cover F.abelian P D m F.level
    L d hd hδ V R hR hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerLocality
