import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange

/-! # Controlled Ideal Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ControlledIdealNaturality.Construction

noncomputable section

/-! Actual controlled ideal sheaves commute with coefficient extension on entire affine blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

def affineControlledIdealSheaf (I J : Ideal R) (b : ℕ) : (ReesGrading.Construction.affineBlowup I).IdealSheafData := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup I) := LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec I)
  exact GlobalControlled.Ideal.Construction.controlledIdealSheaf (QuotientKernel.Construction.affineQuotientKernel I) (QuotientKernel.Construction.affineQuotientKernel J) b (ReesGrading.Construction.affineBlowupToSpec I)

theorem affineControlledIdealSheaf_comap_chart (I J : Ideal R) (b : ℕ) (a : I) :
    (affineControlledIdealSheaf I J b).comap
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide)) =
        QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform I J b a) := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup I) := LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec I)
  let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a) := NoetherianCoordinateTransform.Construction.blowupChart_isNoetherian I a
  rw [affineControlledIdealSheaf, GlobalControlled.Ideal.Construction.controlledIdealSheaf_comap_open]
  unfold GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [Blowup.Charts.Construction.affineBlowup_chart_structureMap, IdealChartDescent.Construction.affineQuotientKernel_comap_hom, IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact GlobalControlled.Chart.Construction.affine_controlled_kernel_identity I J b a

theorem affineControlledIdealSheaf_comap_blowupMap
    {S : Type u} [CommRing S] [IsNoetherianRing S]
    (I J : Ideal R) (b : ℕ) (hJ : J ≤ I ^ b) (φ : R →+* S) :
    (affineControlledIdealSheaf I J b).comap (ReesMap.Construction.affineBlowupMap I φ) =
      affineControlledIdealSheaf (I.map φ) (J.map φ) b := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup (I.map φ)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec (I.map φ))
  let g : I → I.map φ := fun a => ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩
  have hgen : Ideal.span (Set.range (fun a : I => (g a).val)) = I.map φ := by
    have hs : Ideal.span (Set.range (Subtype.val : I → R)) = I := by rw [Subtype.range_val, Ideal.span_eq]
    have h := congrArg (Ideal.map φ) hs
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GeneratedBlowupCover.Construction.affineBlowupGeneratorAffineCover (I.map φ) g hgen).openCover
  intro a
  change I at a
  change ((affineControlledIdealSheaf I J b).comap (ReesMap.Construction.affineBlowupMap I φ)).comap
      (Proj.awayι (ReesGrading.Construction.reesGrade (I.map φ)) (Blowup.Charts.Construction.reesGenerator (I.map φ) (g a))
        (Blowup.Charts.Construction.reesGenerator_mem (I.map φ) (g a)) (by decide)) =
    (affineControlledIdealSheaf (I.map φ) (J.map φ) b).comap
      (Proj.awayι (ReesGrading.Construction.reesGrade (I.map φ)) (Blowup.Charts.Construction.reesGenerator (I.map φ) (g a))
        (Blowup.Charts.Construction.reesGenerator_mem (I.map φ) (g a)) (by decide))
  rw [← Scheme.IdealSheafData.comap_comp, ← Blowup.FlatBaseChange.Construction.affineBlowupMap_chart I φ a,
    Scheme.IdealSheafData.comap_comp, affineControlledIdealSheaf_comap_chart,
    IdealChartDescent.Construction.affineQuotientKernel_comap_hom, affineControlledIdealSheaf_comap_chart]
  exact congrArg QuotientKernel.Construction.affineQuotientKernel (ControlledTransformMap.Construction.blowupChartMap_controlledIdeal I J a φ b hJ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ControlledIdealNaturality.Construction
