import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AcyclicCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.PushforwardSheafNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Cover Pushforward Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.CoverPushforwardCohomology

noncomputable section

/-! A single inverse-image acyclic cover computes cohomology of sheaves on the source by ordered cochains of their direct images. All comparison maps are natural on that fixed source scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (c : R →+* Γ(Y, ⊤))
variable {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (hU : iSup U = ⊤)

def commonCoverPushforwardCohomologyModuleIso (M : X.Modules)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c ((Scheme.Modules.pushforward f).obj M) U).homology (n + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) (n + 1)).obj M :=
  (HomologicalComplex.homologyMapIso (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U)
    (n + 1)).symm ≪≫
      OrderedCech.AcyclicCover.orderedCechAcyclicCoverModuleIso (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i)
        (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) M hM n

theorem commonCoverPushforwardCohomologyModuleIso_naturality
    {M N : X.Modules} (e : M ⟶ N)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (hN : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward f).map e))
        (n + 1) ≫ (commonCoverPushforwardCohomologyModuleIso f c U hU N hN n).hom =
      (commonCoverPushforwardCohomologyModuleIso f c U hU M hM n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) (n + 1)).map e := by
  let eM := HomologicalComplex.homologyMapIso
    (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U) (n + 1)
  let eN := HomologicalComplex.homologyMapIso
    (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c N U) (n + 1)
  let α : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (f.appTop.hom.comp c) M (fun i => f ⁻¹ᵁ U i) ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex (f.appTop.hom.comp c) N (fun i => f ⁻¹ᵁ U i) :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i)).map e
  let β : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c ((Scheme.Modules.pushforward f).obj M) U ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c ((Scheme.Modules.pushforward f).obj N) U :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward f).map e)
  let Ha := HomologicalComplex.homologyMap α (n + 1)
  let Hb := HomologicalComplex.homologyMap β (n + 1)
  have hnat : HomologicalComplex.homologyMap
      ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor (f.appTop.hom.comp c)
        (fun i => f ⁻¹ᵁ U i)).map e) (n + 1) ≫ eN.hom =
    eM.hom ≫ HomologicalComplex.homologyMap
      ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward f).map e))
        (n + 1) := by
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) (n + 1)
    exact (H.map_comp α (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c N U).hom).symm.trans
      ((congrArg H.map (OrderedCech.PushforwardSheafNaturality.orderedCoefficientCechComplexPushforwardIso_sheaf_naturality f c e U)).trans
        (H.map_comp (OrderedCech.PushforwardComplex.orderedCoefficientCechComplexPushforwardIso f c M U).hom β))
  have hinv : HomologicalComplex.homologyMap
      ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward f).map e))
        (n + 1) ≫ eN.inv =
    eM.inv ≫ HomologicalComplex.homologyMap
      ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor (f.appTop.hom.comp c)
        (fun i => f ⁻¹ᵁ U i)).map e) (n + 1) := by
    change Hb ≫ eN.inv = eM.inv ≫ Ha
    have hnat' : Ha ≫ eN.hom = eM.hom ≫ Hb := hnat
    apply (cancel_epi eM.hom).mp
    rw [← Category.assoc, ← hnat', Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  let EM := OrderedCech.AcyclicCover.orderedCechAcyclicCoverModuleIso (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i)
    (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) M hM n
  let EN := OrderedCech.AcyclicCover.orderedCechAcyclicCoverModuleIso (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i)
    (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) N hN n
  let Hc := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.appTop.hom.comp c) (n + 1)).map e
  have hinv' : Hb ≫ eN.inv = eM.inv ≫ Ha := hinv
  have hcoho : Ha ≫ EN.hom = EM.hom ≫ Hc :=
    OrderedCech.AcyclicCover.orderedCechAcyclicCoverModuleIso_naturality (f.appTop.hom.comp c) (fun i => f ⁻¹ᵁ U i)
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top f U hU) e hM hN n
  change Hb ≫ (eN.inv ≫ EN.hom) = (eM.inv ≫ EM.hom) ≫ Hc
  rw [← Category.assoc, hinv', Category.assoc, hcoho, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.CoverPushforwardCohomology
