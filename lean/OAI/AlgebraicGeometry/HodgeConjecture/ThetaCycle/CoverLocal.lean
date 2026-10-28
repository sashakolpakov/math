import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOpenOrientation
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Cover Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocal.CM

noncomputable section

/-! Holomorphic local diffeomorphisms preserve the canonical complex local
orientation. This is derived from the native open-excision and complex
diffeomorphism theorems, without an orientation or local-degree premise. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

variable {d : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [ChartedSpace (Fin d → ℂ) X] [ChartedSpace (Fin d → ℂ) Y]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 Y]

/-- Restriction of an actual partial diffeomorphism to its two open sets. -/
def sheetDiffeomorph
    (φ : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) X Y 1) :
    Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (⟨φ.source, φ.open_source⟩ : Opens X)
      (⟨φ.target, φ.open_target⟩ : Opens Y) 1 where
  toEquiv := φ.toOpenPartialHomeomorph.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    intro x
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (U := (⟨φ.target, φ.open_target⟩ : Opens Y)) _ Set.univ x).mp
    exact contMDiffAt_subtype_iff.mpr
      ((φ.contMDiffOn_toFun x x.property).contMDiffAt
        (φ.open_source.mem_nhds x.property))
  contMDiff_invFun := by
    intro y
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (U := (⟨φ.source, φ.open_source⟩ : Opens X)) _ Set.univ y).mp
    exact contMDiffAt_subtype_iff.mpr
      ((φ.contMDiffOn_invFun y y.property).contMDiffAt
        (φ.open_target.mem_nhds y.property))

theorem sheet_preserves_complex_class
    (φ : PartialDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) X Y 1)
    (x : X) (hx : x ∈ φ.source) :
    (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of X) (Y := TopCat.of Y)
      φ.toOpenPartialHomeomorph x hx (2 * d)).hom
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
        CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (φ x) := by
  let U : Opens X := ⟨φ.source, φ.open_source⟩
  let V : Opens Y := ⟨φ.target, φ.open_target⟩
  let e := φ.toOpenPartialHomeomorph
  have hs : (CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of X) e.source x hx
      e.open_source (2 * d)).inv (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (⟨x, hx⟩ : U) := by
    apply (ConcreteCategory.bijective_of_isIso
      (CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of X) e.source x hx
        e.open_source (2 * d)).hom).1
    rw [Iso.inv_hom_id_apply]
    exact (CycleClass.Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion U ⟨x, hx⟩).symm
  change (CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of Y) e.target (e x)
    (e.map_source hx) e.open_target (2 * d)).hom
      ((CycleClass.Geometric.LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of U) (Y := TopCat.of V)
        e.toHomeomorphSourceTarget (⟨x, hx⟩ : U) (2 * d)).hom
          ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of X) e.source x hx
            e.open_source (2 * d)).inv
              (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x))) = _
  rw [hs]
  have hh := CycleClass.Geometric.ComplexFundamentalNaturality.Cycles.complexCanonicalLocalClass_diffeomorph (sheetDiffeomorph φ) (⟨x, hx⟩ : U)
  change (CycleClass.Geometric.LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of U) (Y := TopCat.of V)
    e.toHomeomorphSourceTarget (⟨x, hx⟩ : U) (2 * d)).hom
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (⟨x, hx⟩ : U)) =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (⟨e x, e.map_source hx⟩ : V) at hh
  rw [hh]
  exact CycleClass.Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion V ⟨e x, e.map_source hx⟩

/-- Actual holomorphic local sheets supply the canonical orientation condition. -/
theorem holomorphic_cover_orientation
    (f : X → Y)
    (hf : IsLocalDiffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 f) :
    ∀ x : X, ∃ (e : OpenPartialHomeomorph X Y) (hx : x ∈ e.source),
      Set.EqOn e f e.source ∧
      (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
        (X := TopCat.of X) (Y := TopCat.of Y) e x hx (2 * d)).hom
        (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
          CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (e x) := by
  intro x
  obtain ⟨φ, hx, hφ⟩ := hf x
  exact ⟨φ.toOpenPartialHomeomorph, hx, hφ.symm,
    sheet_preserves_complex_class φ x hx⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocal.CM
