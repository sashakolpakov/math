import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.GeneratedBlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Chosen Global Rees Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ChosenGlobalReesCover.Construction

noncomputable section

/-! Actual global Rees covers adapted to chosen boundary equation opens and center generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_generated_affineBlowupChart_point
    {R : Type u} [CommRing R] (I : Ideal R) {κ : Type u} (g : κ → I)
    (hgen : Ideal.span (Set.range (fun j => (g j).val)) = I) (x : ReesGrading.Construction.affineBlowup I) :
    ∃ j, ∃ p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I (g j)),
      Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g j)) (Blowup.Charts.Construction.reesGenerator_mem I (g j)) (by decide) p = x := by
  have hx : x ∈ ⨆ j, Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g j)) := by
    rw [GeneratedBlowupCover.Construction.affineBlowup_generator_chart_cover I g hgen]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hrange : x ∈ (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I (g j))
      (Blowup.Charts.Construction.reesGenerator_mem I (g j)) (by decide)).opensRange := by
    rw [Proj.opensRange_awayι]
    exact hj
  obtain ⟨p, hp⟩ := hrange
  exact ⟨j, p, hp⟩

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {ι : Type u} (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).1 = ⊤)
    (κ : ι → Type u) (g : ∀ i, κ i → I.ideal (U i))
    (hgen : ∀ i, Ideal.span (Set.range (fun j => (g i j).val)) = I.ideal (U i))

include hcover hgen in
theorem exists_chosen_globalReesChart (x : GlobalBlowup.Data.Construction.globalBlowup I hI) :
    ∃ p : Σ i, κ i, x ∈ Set.range (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI (U p.1) (g p.1 p.2)) := by
  have hx : GlobalBlowup.Data.Construction.globalBlowupToBase I hI x ∈ ⨆ i, (U i).1 := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hrange : x ∈ (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)).opensRange := by
    rw [GlobalBlowup.MapGluing.Construction.globalBlowupChart_opensRange]
    exact hi
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨j, z, hz⟩ := exists_generated_affineBlowupChart_point (I.ideal (U i)) (g i) (hgen i) y
  refine ⟨⟨i, j⟩, z, ?_⟩
  change GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)
    (Proj.awayι (ReesGrading.Construction.reesGrade (I.ideal (U i))) (Blowup.Charts.Construction.reesGenerator (I.ideal (U i)) (g i j))
      (Blowup.Charts.Construction.reesGenerator_mem (I.ideal (U i)) (g i j)) (by decide) z) = x
  exact (congrArg (GlobalBlowup.Data.Construction.globalBlowupChart I hI (U i)) hz).trans hy

def globalBlowupChosenReesAffineCover : (GlobalBlowup.Data.Construction.globalBlowup I hI).AffineOpenCover where
  I₀ := Σ i, κ i
  X p := .of (Blowup.Charts.Construction.blowupChart (I.ideal (U p.1)) (g p.1 p.2))
  f p := GlobalControlled.Chart.Construction.globalBlowupReesChart I hI (U p.1) (g p.1 p.2)
  idx x := (exists_chosen_globalReesChart I hI U hcover κ g hgen x).choose
  covers x := (exists_chosen_globalReesChart I hI U hcover κ g hgen x).choose_spec

include hcover hgen in
theorem idealSheaf_eq_of_chosen_globalReesCharts (J K : (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData)
    (h : ∀ i j, J.comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI (U i) (g i j)) =
      K.comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI (U i) (g i j))) : J = K :=
  IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover J K (globalBlowupChosenReesAffineCover I hI U hcover κ g hgen).openCover
    (fun p => h p.1 p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ChosenGlobalReesCover.Construction
