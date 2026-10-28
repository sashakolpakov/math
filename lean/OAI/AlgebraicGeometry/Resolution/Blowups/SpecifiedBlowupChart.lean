import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartSpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor

/-! # Specified Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChart.Construction

noncomputable section

/-! Independently named chart maps are the actual restrictions of the affine blowup map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem affineBlowupMapTo_chart (I : Ideal R) (a : I) (φ : R →+* S)
    (K : Ideal S) (hK : I.map φ = K) (b : K) (hb : b.val = φ a.val) :
    Spec.map (CommRingCat.ofHom (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a φ K hK b hb)) ≫
        Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide) =
      Proj.awayι (ReesGrading.Construction.reesGrade K) (Blowup.Charts.Construction.reesGenerator K b) (Blowup.Charts.Construction.reesGenerator_mem K b) (by decide) ≫
        Blowup.Functor.Construction.affineBlowupMapTo I K φ hK := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  exact Blowup.FlatBaseChange.Construction.affineBlowupMap_chart I φ a

theorem affineBlowupMapTo_chart_isPullback (I : Ideal R) (a : I) (φ : R →+* S)
    (K : Ideal S) (hK : I.map φ = K) (b : K) (hb : b.val = φ a.val) :
    IsPullback (Spec.map (CommRingCat.ofHom (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo I a φ K hK b hb)))
      (Proj.awayι (ReesGrading.Construction.reesGrade K) (Blowup.Charts.Construction.reesGenerator K b) (Blowup.Charts.Construction.reesGenerator_mem K b) (by decide))
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide))
      (Blowup.Functor.Construction.affineBlowupMapTo I K φ hK) := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  exact Blowup.FlatBaseChange.Construction.affineBlowupMap_chart_isPullback I φ a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChart.Construction
