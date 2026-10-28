import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ControlledIdealNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing

/-! # Base Change Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.BaseChangeCharts.Construction

noncomputable section

/-! The native global controlled ideal on all actual coefficient-extension Rees charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

local instance (U : X.affineOpens) : IsNoetherianRing Γ(X, U) :=
  IsLocallyNoetherian.component_noetherian U

theorem globalBlowupControlledIdeal_comap_affineBlowup (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (U : X.affineOpens) :
    (Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (GlobalBlowup.Data.Construction.globalBlowupChart I hI U) =
      Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf (I.ideal U) (J.ideal U) b := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup (I.ideal U)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec (I.ideal U))
  rw [Ideal.Construction.globalBlowupControlledIdeal, Ideal.Construction.controlledIdealSheaf_comap_open, GlobalBlowup.Data.Construction.globalBlowupChart_over]
  unfold Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf Ideal.Construction.controlledIdealSheaf
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel]

theorem globalBlowupControlledIdeal_comap_baseChange (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hperm : J ≤ I ^ b) (U : X.affineOpens)
    {S : Type u} [CommRing S] [IsNoetherianRing S] (φ : Γ(X, U) →+* S) :
    (Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap
      (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U) =
        Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf ((I.ideal U).map φ) ((J.ideal U).map φ) b := by
  rw [Scheme.IdealSheafData.comap_comp, globalBlowupControlledIdeal_comap_affineBlowup]
  exact Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf_comap_blowupMap (I.ideal U) (J.ideal U) b (hperm U) φ

def globalBlowupBaseChangeReesChart (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S)
    (a : (I.ideal U).map φ) : Spec (.of (Blowup.Charts.Construction.blowupChart ((I.ideal U).map φ) a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI :=
  Proj.awayι (ReesGrading.Construction.reesGrade ((I.ideal U).map φ)) (Blowup.Charts.Construction.reesGenerator ((I.ideal U).map φ) a)
    (Blowup.Charts.Construction.reesGenerator_mem ((I.ideal U).map φ) a) (by decide) ≫
      (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U)

theorem globalBlowupBaseChangeReesChart_etale (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S) (hφ : φ.Etale)
    (a : (I.ideal U).map φ) : Etale (globalBlowupBaseChangeReesChart I hI U φ a) := by
  let : Algebra Γ(X, U) S := φ.toAlgebra
  let : Algebra.Etale Γ(X, U) S := hφ
  let : Etale (ReesMap.Construction.affineBlowupMap (I.ideal U) φ) := Blowup.FlatBaseChange.Construction.affineBlowupMap_etale (I.ideal U)
  unfold globalBlowupBaseChangeReesChart
  infer_instance

theorem globalBlowupBaseChangeReesChart_over (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) {S : Type u} [CommRing S] (φ : Γ(X, U) →+* S)
    (a : (I.ideal U).map φ) :
    globalBlowupBaseChangeReesChart I hI U φ a ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom ((Blowup.Charts.Construction.blowupChartConstants ((I.ideal U).map φ) a).comp φ)) ≫ U.2.fromSpec := by
  let c := Proj.awayι (ReesGrading.Construction.reesGrade ((I.ideal U).map φ)) (Blowup.Charts.Construction.reesGenerator ((I.ideal U).map φ) a)
    (Blowup.Charts.Construction.reesGenerator_mem ((I.ideal U).map φ) a) (by decide)
  have hc : c ≫ ReesGrading.Construction.affineBlowupToSpec ((I.ideal U).map φ) =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants ((I.ideal U).map φ) a)) :=
    Blowup.Charts.Construction.affineBlowup_chart_structureMap ((I.ideal U).map φ) a
  change (c ≫ (ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ GlobalBlowup.Data.Construction.globalBlowupChart I hI U)) ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = _
  calc
    _ = c ≫ ((ReesMap.Construction.affineBlowupMap (I.ideal U) φ ≫ ReesGrading.Construction.affineBlowupToSpec (I.ideal U)) ≫ U.2.fromSpec) := by
      simp only [Category.assoc, GlobalBlowup.Data.Construction.globalBlowupChart_over]
    _ = (c ≫ ReesGrading.Construction.affineBlowupToSpec ((I.ideal U).map φ)) ≫ Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec := by
      rw [Blowup.BaseOpen.Construction.affineBlowupMap_over]
      simp only [Category.assoc]
    _ = _ := by
      rw [hc, ← Category.assoc, ← Spec.map_comp]
      rfl

theorem globalBlowupControlledIdeal_comap_baseChangeReesChart (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hperm : J ≤ I ^ b) (U : X.affineOpens)
    {S : Type u} [CommRing S] [IsNoetherianRing S] (φ : Γ(X, U) →+* S)
    (a : (I.ideal U).map φ) :
    (Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (globalBlowupBaseChangeReesChart I hI U φ a) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform ((I.ideal U).map φ) ((J.ideal U).map φ) b a) := by
  rw [globalBlowupBaseChangeReesChart, Scheme.IdealSheafData.comap_comp,
    globalBlowupControlledIdeal_comap_baseChange I J hI b hperm,
    Affine.ControlledIdealNaturality.Construction.affineControlledIdealSheaf_comap_chart]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.BaseChangeCharts.Construction
