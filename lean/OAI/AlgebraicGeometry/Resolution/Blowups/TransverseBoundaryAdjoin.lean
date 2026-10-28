import OAI.AlgebraicGeometry.Resolution.Blowups.FixedNormalBoundaryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.AdjoinCoordinate
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.EquationCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Transverse Boundary Adjoin -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The full local boundary admits a transverse hypersurface as an additional labelled component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def TransverseBoundaryOpen.Construction.TransverseBoundaryOpenChart.adjoinEquation
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {w : ι → R} {z : R} {p : PrimeSpectrum R}
    (C : TransverseBoundaryOpen.Construction.TransverseBoundaryOpenChart k R w z p) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R (fun j : Option ι => match j with | none => z | some j => w j) p := by
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  let N := C.chart.model.adjoinEquation (C.chart.map z) C.normalIndex C.normal_unused C.normal_eq
  exact { carrier := C.chart.carrier
          algebra := C.chart.algebra
          map := C.chart.map
          isOpenImmersion := C.chart.isOpenImmersion
          point := C.chart.point
          point_over := C.chart.point_over
          model := N.congrEquations (fun j => C.chart.map (v j)) (by intro j; cases j <;> rfl) }

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.hasEtaleBoundaryCharts_adjoin_transverse
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (z : R) (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z = 1) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j) := by
  intro p
  obtain ⟨C⟩ := FixedNormalBoundaryOpen.Construction.exists_fixed_normal_boundary_open R w M E hE z hEz p
  exact ⟨C.adjoinEquation⟩

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.adjoin_transverse_equation
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (z : R) (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z = 1) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R (fun j : Option ι => match j with | none => z | some j => w j) := by
  intro p
  obtain ⟨C⟩ := h p
  have hf : C.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)))
  let : Algebra R C.carrier := C.map.toRingHom.toAlgebra
  let : IsScalarTower k R C.carrier :=
    IsScalarTower.of_algebraMap_eq (fun c => (C.map.commutes c).symm)
  let : Algebra.Etale R C.carrier := RingHom.etale_algebraMap.mp hf
  let D := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := C.carrier) E
  have hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => C.map (w j)) :=
    Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := C.carrier) k w ⟨E, hE⟩
  have hDz : D (C.map z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := C.carrier) E (algebraMap R C.carrier z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hEz, map_one]
  obtain ⟨A⟩ := C.model.hasEtaleBoundaryCharts_adjoin_transverse (C.map z) D hD hDz C.point
  exact ⟨A.comp C.map (fun j : Option ι => match j with | none => z | some j => w j)
    (by intro j; cases j <;> rfl) p C.point_over⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
