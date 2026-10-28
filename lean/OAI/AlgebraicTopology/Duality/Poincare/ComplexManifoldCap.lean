import OAI.AlgebraicTopology.Duality.Poincare.SupportCapNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental

/-! # Complex Manifold Cap -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap

noncomputable section

/-!
# Cap with the canonical complex orientation

The compact-support relative fundamental classes used here were constructed
from the actual complex local generators and finite chart gluing. Their
proved restriction compatibility makes the genuine relative cap maps descend
to compact-support singular cohomology. No orientation class or duality map
is supplied as an assumption.

This file constructs the canonical cap map. It does not yet assert that this
map is an isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) 1 M]

/-- The constructed complex fundamental class, reindexed to an equal
homological degree. This only transports the actual relative homology object. -/
def complexCompactClassInDegree (d : ℕ) (hd : d = 2 * n) (K : Compacts M) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ d :=
  (eqToHom (congrArg
    (fun j => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ j) hd.symm))
      (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass n (K : Set M) K.isCompact)

@[simp]
theorem complexCompactClassInDegree_top (K : Compacts M) :
    complexCompactClassInDegree n (2 * n) rfl K =
      AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass n (K : Set M) K.isCompact := rfl

/-- Reindexing preserves the proved restriction compatibility of the
canonical integral compact-support classes. -/
theorem complexCompactClassInDegree_restriction (d : ℕ) (hd : d = 2 * n)
    {K L : Compacts M} (h : K ≤ L) :
    AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) h d
        (complexCompactClassInDegree n d hd L) =
      complexCompactClassInDegree n d hd K := by
  subst d
  exact AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_restriction n
    (K : Set M) (L : Set M) K.isCompact L.isCompact h

/-- Cap with the canonical complex orientation, on actual compact-support
rational cohomology and ordinary rational singular homology. -/
def complexManifoldCompactSupportCap (p q : ℕ) (hpq : p + q = 2 * n) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ⟶
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q :=
  SupportCapNaturality.compactSupportedCapOfCompatibleClasses (TopCat.of M) p q
    (complexCompactClassInDegree n (p + q) hpq)
    (fun _ _ h => complexCompactClassInDegree_restriction n (p + q) hpq h)

/-- The canonical cap map is computed at every compact support using the
constructed integral relative fundamental class. -/
@[reassoc (attr := simp)]
theorem complexManifoldCompactSupportCap_stage (p q : ℕ) (hpq : p + q = 2 * n)
    (K : Compacts M) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K p ≫
        complexManifoldCompactSupportCap n (M := M) p q hpq =
      SupportCapNaturality.relativeCapWithClass (TopCat.of M) (K : Set M)ᶜ p q
        (complexCompactClassInDegree n (p + q) hpq K) :=
  SupportCapNaturality.compactSupportedCapOfCompatibleClasses_stage (TopCat.of M) p q _ _ K

/-- Elementwise computation of the canonical cap map on a supported class. -/
@[simp]
theorem complexManifoldCompactSupportCap_stage_apply (p q : ℕ) (hpq : p + q = 2 * n)
    (K : Compacts M)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ p) :
    complexManifoldCompactSupportCap n (M := M) p q hpq
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K p c) =
      SupportRelativeCap.relativeCapHomology (TopCat.of M) (K : Set M)ᶜ p q c
        (complexCompactClassInDegree n (p + q) hpq K) :=
  ConcreteCategory.congr_hom
    (complexManifoldCompactSupportCap_stage n p q hpq K) c

/-- On coordinate space itself, the chart-independent complex generator
is the coordinate generator used in the closed-ball normalization. -/
theorem complexCanonicalLocalClass_eq_coordinate (x : Fin n → ℂ) :
    AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := n) x = AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.complexCoordinatePointClass n x := by
  let e := OpenPartialHomeomorph.refl (Fin n → ℂ)
  have he : e ∈ atlas (Fin n → ℂ) (Fin n → ℂ) := by
    simpa only [chartAt_self_eq] using chart_mem_atlas (Fin n → ℂ) x
  have hx : x ∈ e.source := Set.mem_univ x
  have hi := AlgebraicGeometry.CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_id
    (X := TopCat.of (Fin n → ℂ)) e x hx (fun _ _ => rfl) (2 * n)
  have hid : (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of (Fin n → ℂ)) (Y := TopCat.of (Fin n → ℂ)) e x hx (2 * n)).hom =
      𝟙 _ := by
    change (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of (Fin n → ℂ)) (Y := TopCat.of (Fin n → ℂ)) e x hx (2 * n)).hom ≫
        𝟙 _ = 𝟙 _ at hi
    simpa only [Category.comp_id] using hi
  have h := AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison.Cycles.complexCanonicalLocalClass_chart e he x hx
  rw [hid] at h
  exact h

/-- The constructed manifold orientation agrees with the original concrete
coordinate compact-support class, fixing the normalization used by the
Euclidean compact-support cohomology calculation. -/
theorem complexCompactFundamentalClass_eq_coordinate
    (K : Set (Fin n → ℂ)) (hK : IsCompact K) :
    AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass n K hK = AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass n K hK := by
  symm
  apply AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique n K hK
  intro x hx
  rw [AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint, complexCanonicalLocalClass_eq_coordinate]

end

end OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
