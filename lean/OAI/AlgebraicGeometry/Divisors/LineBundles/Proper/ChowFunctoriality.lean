import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass

/-! # Chow Functoriality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowFunctoriality.BundleCycles

noncomputable section

/-! Functoriality and compatibility of actual proper Chow pushforward,
including explicit transport between structure morphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (i : X ⟶ Y) [IsProper i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (h : i ≫ g = f)

def properChowPushforwardOver (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g d :=
  (ChowNe.BundleCycles.properChowPushforward i g d).comp (DimensionChow.BundleCycles.dimensionChowTransport h.symm d)

theorem properChowPushforwardOver_pointClass (d : ℕ) (z : X →₀ ℚ) :
    properChowPushforwardOver i f g h d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ g d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) := by
  change ChowNe.BundleCycles.properChowPushforward i g d (DimensionChow.BundleCycles.dimensionChowTransport h.symm d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z)) = _
  rw [Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, ChowNe.BundleCycles.properChowPushforward_pointClass]

theorem properChowPushforward_eq_finite [IsFinite i] (d : ℕ) :
    ChowNe.BundleCycles.properChowPushforward i g d = Finite.ChowPushforward.BundleCycles.finiteChowPushforward i g d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ g) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (i ≫ g) d z,
    ChowNe.BundleCycles.properChowPushforward_pointClass, Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass]

theorem properChowPushforward_eq_closed [IsClosedImmersion i] (d : ℕ) :
    ChowNe.BundleCycles.properChowPushforward i g d = Closed.ChowPushforward.BundleCycles.closedChowPushforward i g d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ g) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (i ≫ g) d z,
    ChowNe.BundleCycles.properChowPushforward_pointClass, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion]

theorem properChowPushforwardOver_comp {Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Z]
    [Z.IsSeparated] (j : Y ⟶ Z) [IsProper j] (k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType k]
    (hj : j ≫ k = g) (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    properChowPushforwardOver j g k hj d (properChowPushforwardOver i f g h d α) =
      properChowPushforwardOver (i ≫ j) f k (by rw [Category.assoc, hj, h]) d α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, properChowPushforwardOver_pointClass,
    properChowPushforwardOver_pointClass, properChowPushforwardOver_pointClass,
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]

theorem properChowPushforwardOver_id (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ g d) :
    properChowPushforwardOver (𝟙 Y) g g (Category.id_comp g) d α = α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective g d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion g d z, properChowPushforwardOver_pointClass]
  rw [IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion]
  change Point.CycleChow.BundleCycles.pointCycleToChowQ g d (Finsupp.mapDomain id _) = _
  rw [Finsupp.mapDomain_id]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowFunctoriality.BundleCycles
