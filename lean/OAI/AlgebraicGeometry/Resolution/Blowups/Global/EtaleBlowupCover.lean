import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.BaseChangeCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.ChosenGlobalReesCover

/-! # Etale Blowup Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.EtaleBlowupCover.Construction

noncomputable section

/-! Actual global blowup charts obtained from covering étale coefficient algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowup_baseChange_isPullback (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) (hφ : φ.Flat) :
    IsPullback (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U)
      (ReesGrading.Construction.affineBlowupToSpec ((I.ideal U).map φ)) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
      (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) := by
  let : Algebra Γ(X, U) S := φ.toAlgebra
  let : Module.Flat Γ(X, U) S := hφ
  exact ((Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback (S := S) (I.ideal U)).flip.paste_vert
    (GlobalBlowup.MapGluing.Construction.globalBlowup_affineSpec_isPullback I hI U).flip).flip

theorem exists_globalBlowup_baseChange_lift (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) (hφ : φ.Flat)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (q : PrimeSpectrum S)
    (hq : GlobalBlowup.Data.Construction.globalBlowupToBase I hI x = (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) q) :
    ∃ y : ReesGrading.Construction.affineBlowup ((I.ideal U).map φ),
      (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U) y = x ∧
        ReesGrading.Construction.affineBlowupToSpec ((I.ideal U).map φ) y = q :=
  Scheme.exists_preimage_of_isPullback (globalBlowup_baseChange_isPullback I hI U φ hφ) x q hq

theorem exists_generated_globalBlowup_baseChangeReesChart
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (U : X.affineOpens)
    {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) (hφ : φ.Flat)
    {κ : Type u} (g : κ → (I.ideal U).map φ)
    (hgen : Ideal.span (Set.range (fun j => (g j).val)) = (I.ideal U).map φ)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (q : PrimeSpectrum S)
    (hq : GlobalBlowup.Data.Construction.globalBlowupToBase I hI x = (Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec) q) :
    ∃ j, ∃ p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ) (g j)),
      GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI U φ (g j) p = x := by
  obtain ⟨y, hy, _⟩ := exists_globalBlowup_baseChange_lift I hI U φ hφ x q hq
  obtain ⟨j, p, hp⟩ := ChosenGlobalReesCover.Construction.exists_generated_affineBlowupChart_point ((I.ideal U).map φ) g hgen y
  refine ⟨j, p, ?_⟩
  change (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U)
    (Proj.awayι (ReesGrading.Construction.reesGrade ((I.ideal U).map φ)) (Blowup.Charts.Construction.reesGenerator ((I.ideal U).map φ) (g j))
      (Blowup.Charts.Construction.reesGenerator_mem ((I.ideal U).map φ) (g j)) (by decide) p) = x
  exact (congrArg (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U) hp).trans hy

theorem exists_globalBlowup_etaleReesChart_of_cover
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type u} (U : ι → X.affineOpens)
    (S : ι → Type u) [∀ i, CommRing (S i)] (φ : ∀ i, Γ(X, U i) →+* S i)
    (hφ : ∀ i, (φ i).Etale)
    (hcover : ∀ x : X, ∃ i, ∃ q : PrimeSpectrum (S i),
      (Spec.map (CommRingCat.ofHom (φ i)) ≫ (U i).2.fromSpec) q = x)
    (κ : ι → Type u) (g : ∀ i, κ i → (I.ideal (U i)).map (φ i))
    (hgen : ∀ i, Ideal.span (Set.range (fun j => (g i j).val)) = (I.ideal (U i)).map (φ i))
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) :
    ∃ i, ∃ j, ∃ p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart ((I.ideal (U i)).map (φ i)) (g i j)),
      GlobalControlled.BaseChangeCharts.Construction.globalBlowupBaseChangeReesChart I hI (U i) (φ i) (g i j) p = x := by
  obtain ⟨i, q, hq⟩ := hcover (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x)
  obtain ⟨j, p, hp⟩ := exists_generated_globalBlowup_baseChangeReesChart I hI (U i) (φ i)
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp (hφ i)).1 (g i) (hgen i) x q hq.symm
  exact ⟨i, j, p, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.EtaleBlowupCover.Construction
