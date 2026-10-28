import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapTransitions
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.PhaseLeaves

/-! # Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Overlap.Construction

noncomputable section

/-! Original-ground algebra structures on genuine blowup-chart overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

theorem blowupChartOverlapLeft_etale : (ChartOverlap.Construction.blowupChartOverlapLeft I a b).Etale := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapLeft I a b))) :=
    ChartOverlap.Construction.blowupChartOverlapLeft_isOpenImmersion I a b
  have h : Etale (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapLeft I a b))) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h

theorem blowupChartOverlapRight_etale : (ChartOverlap.Construction.blowupChartOverlapRight I a b).Etale := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapRight I a b))) :=
    ChartOverlap.Construction.blowupChartOverlapRight_isOpenImmersion I a b
  have h : Etale (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapRight I a b))) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h

variable (k : Type u) [CommRing k] [Algebra k R]

abbrev blowupOverlapBaseAlgebra : Algebra k (ChartOverlap.Construction.blowupChartOverlap I a b) :=
  ((ChartOverlap.Construction.blowupChartOverlapConstants I a b).comp (algebraMap k R)).toAlgebra

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra blowupOverlapBaseAlgebra

def blowupChartOverlapLeftAlgHom : Charts.Construction.blowupChart I a →ₐ[k] ChartOverlap.Construction.blowupChartOverlap I a b where
  toRingHom := ChartOverlap.Construction.blowupChartOverlapLeft I a b
  commutes' c := ChartOverlap.Construction.blowupChartOverlapLeft_constants I a b (algebraMap k R c)

def blowupChartOverlapRightAlgHom : Charts.Construction.blowupChart I b →ₐ[k] ChartOverlap.Construction.blowupChartOverlap I a b where
  toRingHom := ChartOverlap.Construction.blowupChartOverlapRight I a b
  commutes' c := ChartOverlap.Construction.blowupChartOverlapRight_constants I a b (algebraMap k R c)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Overlap.Construction
