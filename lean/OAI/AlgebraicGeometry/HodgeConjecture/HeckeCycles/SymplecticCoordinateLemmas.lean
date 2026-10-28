import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap

/-! # Symplectic Coordinate Lemmas -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas.CM

noncomputable section

/-! Coordinate formulas with the ring and equality decisions kept
abstract, so concrete adelic applications do not unfold ring instances. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I K L : Type*} [Fintype I] [CommRing K] [CommRing L]

theorem reindex_refl_matrix (d₁ d₂ : DecidableEq I) (g : @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I _ d₁ K _) :
    (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex I I K _ _ d₁ d₂ _ (Equiv.refl I) g).val = g.val := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem swap_matrix [DecidableEq I] (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom g).val = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap := rfl

theorem map_matrix [DecidableEq I] (f : K →+* L) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g).val = g.val.map f := rfl

theorem reindex_map_swap_matrix (d₁ d₂ : DecidableEq I) (f : K →+* L) (g : @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I _ d₁ K _) :
    (@RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom I L _ d₂ _
      (@RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp I _ d₂ K L _ _ f (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex I I K _ _ d₁ d₂ _ (Equiv.refl I) g))).val =
    @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap I d₂ L _ * g.val.map f * @RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap I d₂ L _ := by
  rw [swap_matrix, map_matrix, reindex_refl_matrix]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas.CM
