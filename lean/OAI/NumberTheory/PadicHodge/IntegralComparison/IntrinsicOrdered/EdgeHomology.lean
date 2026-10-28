import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeAdditive
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Edge Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates

noncomputable section

/-! Homology coordinates of the native Čech global edge. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (K : CochainComplex X.Modules ℕ) (q : ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)

def sectionIso : (G).obj ((OrderedCech.Total.Comparison.sectionComplex π K).homology q) ≅
    (Presheaf.OrderedCechEdge.sections (Relative.AdditiveCechConcentration.coefficients K)).homology q :=
  (((OrderedCech.Total.Comparison.sectionComplex π K).sc q).mapHomologyIso G).symm

abbrev homology := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
  (Iso.refl _) (CechAdditiveCoordinates.Intrinsic.totalIso π U K)
  (OrderedCech.Total.Comparison.edge π U K hU)
  (Presheaf.OrderedCechEdge.edge U (Relative.AdditiveCechConcentration.coefficients K))
  ((EdgeAdditive.IntrinsicCoordinates.additive π U hU K).trans (Category.id_comp _).symm) q

omit [X.IsSeparated] in
theorem homology_coordinates :
    (G).map (homologyMap (OrderedCech.Total.Comparison.edge π U K hU) q) ≫
      (CechAdditiveCoordinates.Intrinsic.homologyIso π U K q).hom =
    (sectionIso π K q).hom ≫
      homologyMap (Presheaf.OrderedCechEdge.edge U (Relative.AdditiveCechConcentration.coefficients K)) q := by
  have h := IntrinsicCoordinates.homology π U hU K q
  change (G).map (homologyMap (OrderedCech.Total.Comparison.edge π U K hU) q) ≫
    (CechAdditiveCoordinates.Intrinsic.homologyIso π U K q).hom =
      ((sectionIso π K q).hom ≫ homologyMap (𝟙 _) q) ≫
        homologyMap (Presheaf.OrderedCechEdge.edge U
          (Relative.AdditiveCechConcentration.coefficients K)) q at h
  simpa only [homologyMap_id, Category.comp_id] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeHomology.IntrinsicCoordinates
