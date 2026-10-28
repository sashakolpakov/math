import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionSpecialization

/-! # Intersection Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionSupport.Cycles

noncomputable section

/-! Line-bundle intersection stays in the specialization closure
of its input support, including on singular integral supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem lineBundleDivisorOnPoint_specializes (x y : X)
    (hy : Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x) y ≠ 0) : x ⤳ y := by
  apply specializes_iff_mem_closure.mpr
  have hr : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) := by
    by_contra hn
    exact hy (Finsupp.mapDomain_of_notMem_range _ _ hn)
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι] at hr
  exact hr

theorem lineBundlePointIntersection_support_stable (P : X → Prop)
    (hP : ∀ {x y : X}, x ⤳ y → P x → P y) (z : X →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → P x) :
    ∀ y, Intersection.Cycles.lineBundlePointIntersection L z y ≠ 0 → P y := by
  classical
  intro y hy
  by_contra hny
  apply hy
  rw [Intersection.Cycles.lineBundlePointIntersection, Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro x hx
  have hd : Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x) y = 0 := by
    by_contra hd
    exact hny (hP (lineBundleDivisorOnPoint_specializes L x y hd) (hz x (Finsupp.mem_support_iff.mp hx)))
  simp only [Finsupp.smul_apply, hd, smul_zero]

theorem lineBundlePointIntersection_image_dimension_bound
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] (p : X ⟶ Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ) (z : X →₀ ℚ)
    (hz : ∀ x, z x ≠ 0 → Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f ≤ d) :
    ∀ y, Intersection.Cycles.lineBundlePointIntersection L z y ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p y)) f ≤ d :=
  lineBundlePointIntersection_support_stable L _
    (fun hs hx => (Point.DimensionSpecialization.BundleCycles.pointClosure_dimension_specializes f (hs.map p.continuous)).trans hx) z hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionSupport.Cycles
