import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftCharts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.LiftGluedReduction

/-! # Source Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLift

noncomputable section

/-! A genuine global etale lift of an affine etale morphism across a
nilpotent closed target thickening, assembled from its actual standard
etale charts. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X₀ X Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (f : Y₀ ⟶ X₀) [Etale f] [IsAffineHom f]

abbrev Index := LiftCharts.Index i f

def localChart (a : Index i f) : LiftOverlap.Chart i f where
  base := a.1.1.toScheme
  base_affine := a.1.2
  baseMap := a.1.1.ι
  base_open := inferInstance
  scheme := LiftCharts.chart i f a
  affine := inferInstance
  map := LiftCharts.chartBase i f a
  etale := inferInstance
  reduced := LiftCharts.reducedChart i f a
  reduction := LiftCharts.reduction i f a
  closed := inferInstance
  surjective := LiftCharts.reduction_surjective i hi f a
  nilpotent := LiftCharts.reduction_nilpotent i hi f a
  source := LiftCharts.sourceMap i f a
  source_open := inferInstance
  «over» := LiftCharts.reduction_over i f a

abbrev source : Scheme.{u} := LiftGluedMap.Overlap.glued (localChart i hi f)

def map : SourceLift.source i hi f ⟶ X := LiftGluedMap.Overlap.map (localChart i hi f)
instance map_etale : Etale (SourceLift.map i hi f) := LiftGluedMap.Overlap.map_etale (localChart i hi f)

def reduction : Y₀ ⟶ SourceLift.source i hi f :=
  LiftGluedMap.Overlap.reduction (localChart i hi f) (LiftCharts.sourceMap_covers i f)

theorem reduction_map : SourceLift.reduction i hi f ≫ SourceLift.map i hi f = f ≫ i :=
  LiftGluedMap.Overlap.reduction_map (localChart i hi f) (LiftCharts.sourceMap_covers i f)

theorem reduction_surjective : Function.Surjective (SourceLift.reduction i hi f) :=
  LiftGluedReduction.Overlap.reduction_surjective (localChart i hi f) (LiftCharts.sourceMap_covers i f)

instance reduction_closed : IsClosedImmersion (SourceLift.reduction i hi f) :=
  LiftGluedReduction.Overlap.reduction_closed (localChart i hi f) (LiftCharts.sourceMap_covers i f)

def reductionHomeomorph : Y₀ ≃ₜ SourceLift.source i hi f :=
  LiftGluedReduction.Overlap.reductionHomeomorph (localChart i hi f) (LiftCharts.sourceMap_covers i f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SourceLift
