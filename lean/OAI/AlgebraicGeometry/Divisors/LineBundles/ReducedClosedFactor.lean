import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Reduced Closed Factor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ReducedClosedFactor.BundleCycles

noncomputable section

/-! A map from a reduced scheme factors through a closed subscheme whenever
its actual topological image lies in that subscheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

theorem closedImmersion_ker_le_of_reduced_range {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion i] [IsReduced Y]
    [QuasiCompact g] (h : Set.range g ⊆ Set.range i) : i.ker ≤ g.ker := by
  have hs : g.ker.support ≤ i.ker.support := by
    change (g.ker.support : Set Z) ⊆ (i.ker.support : Set Z)
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    exact closure_mono h
  have hk := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support, CycleClass.Geometric.StratumClosure.kernel_radical_of_reduced g] at hk
  exact hk

def reducedClosedFactor {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion i] [IsReduced Y]
    [QuasiCompact g] (h : Set.range g ⊆ Set.range i) : Y ⟶ X :=
  IsClosedImmersion.lift i g (closedImmersion_ker_le_of_reduced_range i g h)

theorem reducedClosedFactor_comp {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion i] [IsReduced Y]
    [QuasiCompact g] (h : Set.range g ⊆ Set.range i) :
    reducedClosedFactor i g h ≫ i = g :=
  IsClosedImmersion.lift_fac i g _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ReducedClosedFactor.BundleCycles
