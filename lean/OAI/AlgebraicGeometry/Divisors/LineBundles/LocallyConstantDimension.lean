import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenPointChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import Mathlib.Topology.LocallyConstant.Basic

/-! # Locally Constant Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyConstantDimension.BundleCycles

noncomputable section

/-! Selecting point dimensions relative to a locally constant geometric
dimension label preserves equality in each actual Chow dimension grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)

omit [LocallyOfFiniteType f] in
theorem pointCycleToChowQ_setPart_eq_of_agreeOnGrade (S T : Set X)
    (hST : ∀ x, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d →
      (x ∈ S ↔ x ∈ T)) (z : X →₀ ℚ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Point.CycleSet.BundleCycles.pointCycleSetPart S z) = Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Point.CycleSet.BundleCycles.pointCycleSetPart T z) := by
  apply congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ f d)
  ext Z
  change Point.CycleSet.BundleCycles.pointCycleSetPart S z (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d Z) =
    Point.CycleSet.BundleCycles.pointCycleSetPart T z (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d Z)
  have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d Z)) f = d := Z.property
  by_cases hx : Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d Z ∈ S
  · rw [Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem _ _ _ hx,
      Point.CycleSet.BundleCycles.pointCycleSetPart_apply_mem _ _ _ ((hST _ hd).mp hx)]
  · rw [Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem _ _ _ hx,
      Point.CycleSet.BundleCycles.pointCycleSetPart_apply_notMem _ _ _ (fun h => hx ((hST _ hd).mpr h))]

theorem locallyConstantDimensionPart_chow_eq (N : X → ℕ) (hN : IsLocallyConstant N) (p : ℕ)
    (z w : X →₀ ℚ) (hzw : Point.CycleChow.BundleCycles.pointCycleToChowQ f d z = Point.CycleChow.BundleCycles.pointCycleToChowQ f d w) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d
        (Point.CycleSet.BundleCycles.pointCycleSetPart {x | Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + p = N x} z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d
        (Point.CycleSet.BundleCycles.pointCycleSetPart {x | Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + p = N x} w) := by
  let U : X.Opens := ⟨{x | N x = d + p}, hN.isOpen_fiber (d + p)⟩
  let : AlgebraicGeometry.IsNoetherian U.toScheme := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian U.ι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hN.isClosed_fiber (d + p))
  have hS : ∀ x, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d →
      (x ∈ {x | Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + p = N x} ↔
        x ∈ Set.range U.ι) := by
    intro x hx
    rw [Scheme.Opens.range_ι]
    change _ + p = N x ↔ N x = d + p
    rw [hx]
    exact eq_comm
  exact (pointCycleToChowQ_setPart_eq_of_agreeOnGrade f d _ _ hS z).trans
    ((ClopenPointChow.BundleCycles.clopenPointChowPart_eq_of_eq U.ι f d z w hzw).trans
      (pointCycleToChowQ_setPart_eq_of_agreeOnGrade f d _ _ hS w).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyConstantDimension.BundleCycles
