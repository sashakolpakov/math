import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin

/-! # Pair Pullback Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PairPullbackClass.BundleCycles

noncomputable section

/-! The normalized normal classes are functorial under an actual map of
normal neighborhoods that preserves their normal-coordinate functions. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalFin.Cycles

variable {M N M' N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : M → N} {v : M' → N'} {x : M} {y : M'} {p : ℕ}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin p → ℂ) v y)

theorem normalPairClass_pullback (g : TopCat.of Q.neighborhood ⟶ TopCat.of P.neighborhood)
    (hg : Set.MapsTo g Q.relativeComplement P.relativeComplement)
    (hn : g ≫ P.normalCoordinate = Q.normalCoordinate) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * p) P.rationalClassFin =
      Q.rationalClassFin := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) g P.normalCoordinate hg
      P.normalCoordinate_mapsTo (2 * p)) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  have he : ∀ (k : TopCat.of Q.neighborhood ⟶ TopCat.of (Fin p → ℂ))
      (hk : k = Q.normalCoordinate) (hkm : Set.MapsTo k Q.relativeComplement {0}ᶜ),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k hkm (2 * p)
        (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) =
      Q.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
    intro k hk hkm
    subst k
    rfl
  exact h.trans (he _ hn _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PairPullbackClass.BundleCycles
