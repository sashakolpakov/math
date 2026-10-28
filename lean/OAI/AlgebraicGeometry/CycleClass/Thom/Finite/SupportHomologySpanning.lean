import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual

/-! # Support Homology Spanning -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportHomologySpanning.Constructions

noncomputable section

/-! Top homology supported on finitely many points is spanned by the actual inserted local orientations. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

def pointCoefficient (K : Set M) (x : K)
    (a : Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d)) : ℤ :=
  (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass_generates (p := d) x.val
    (Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val x.property (2 * d) a)).choose

omit [T2Space M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] in
theorem pointCoefficient_spec (K : Set M) (x : K)
    (a : Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d)) :
    pointCoefficient d K x a • Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x.val =
      Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val x.property (2 * d) a :=
  (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass_generates (p := d) x.val
    (Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val x.property (2 * d) a)).choose_spec.1

theorem finiteSupport_spanning (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (y : U x), y.val ∈ K → y.val = x.val)
    (a : Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d)) :
    (∑ x : K, pointCoefficient d K x a •
      ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
        (fun y hy => Subtype.ext (hUK x y hy)) (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)) = a := by
  classical
  apply Geometric.ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext d K (Set.toFinite K).isCompact
  intro z hz
  rw [map_sum]
  rw [Finset.sum_eq_single (⟨z, hz⟩ : K)]
  · rw [map_zsmul]
    exact (congrArg (fun t => pointCoefficient d K ⟨z, hz⟩ a • t)
      (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion_fundamental_self d K (U ⟨z, hz⟩)
        ⟨z, hxU ⟨z, hz⟩⟩ hz _)).trans (pointCoefficient_spec d K ⟨z, hz⟩ a)
  · intro x _ hx
    rw [map_zsmul]
    have hzx : z ≠ x.val := fun h => hx (Subtype.ext h.symm)
    have h := ConcreteCategory.congr_hom
      (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion_to_other K (U x) ⟨x.val, hxU x⟩
        (fun y hy => Subtype.ext (hUK x y hy)) z hz hzx (2 * d))
      (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)
    refine (congrArg (fun t => pointCoefficient d K x a • t) h).trans ?_
    change pointCoefficient d K x a • (0 : Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) z (2 * d)) = 0
    exact zsmul_zero _
  · simp

theorem functional_ext (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (y : U x), y.val ∈ K → y.val = x.val)
    {V : Type} [AddCommGroup V] [Module ℤ V]
    (F G : Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d) →ₗ[ℤ] V)
    (h : ∀ x : K,
      F (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
        (fun y hy => Subtype.ext (hUK x y hy)) (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)) =
      G (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
        (fun y hy => Subtype.ext (hUK x y hy)) (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩))) : F = G := by
  ext a
  rw [← finiteSupport_spanning d K U hxU hUK a, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, map_zsmul, h x]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportHomologySpanning.Constructions
