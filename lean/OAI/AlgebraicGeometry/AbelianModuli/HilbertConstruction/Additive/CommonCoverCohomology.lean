import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CechPushforwardNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CohomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Common Cover Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverCohomology

noncomputable section

/-! A common inverse-image acyclic cover computes genuine sheaf cohomology naturally for arbitrary additive-sheaf maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {X P : Scheme.{u}} (a : P ⟶ X)
variable {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)

def additiveCommonCoverCohomologyIso (F : P.carrier.Sheaf AddCommGrpCat.{u})
    (hF : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ U i) F) (n : ℕ) :
    ((cechComplexFunctor U).obj ((Opens.map a.base).op ⋙ F.obj)).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).obj F :=
  (HomologicalComplex.homologyMapIso (CechPushforward.additiveCechPushforwardComplexIso a F.obj U) (n + 1)).symm ≪≫
    IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections (fun i => a ⁻¹ᵁ U i) F
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) hF n

theorem additiveCommonCoverCohomologyIso_naturality
    {F G : P.carrier.Sheaf AddCommGrpCat.{u}} (e : F ⟶ G)
    (hF : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ U i) F)
    (hG : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ U i) G) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e.hom)) (n + 1) ≫
        (additiveCommonCoverCohomologyIso a U hU G hG n).hom =
      (additiveCommonCoverCohomologyIso a U hU F hF n).hom ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).map e := by
  have hi : HomologicalComplex.homologyMap
      ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e.hom)) (n + 1) ≫
        HomologicalComplex.homologyMap (CechPushforward.additiveCechPushforwardComplexIso a G.obj U).inv (n + 1) =
      HomologicalComplex.homologyMap (CechPushforward.additiveCechPushforwardComplexIso a F.obj U).inv (n + 1) ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).map e.hom) (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      CechPushforwardNaturality.additiveCechPushforwardComplexIso_inv_naturality]
  let pF := HomologicalComplex.homologyMap
    (CechPushforward.additiveCechPushforwardComplexIso a F.obj U).inv (n + 1)
  let pG := HomologicalComplex.homologyMap
    (CechPushforward.additiveCechPushforwardComplexIso a G.obj U).inv (n + 1)
  let k := HomologicalComplex.homologyMap
    ((cechComplexFunctor U).map (Functor.whiskerLeft (Opens.map a.base).op e.hom)) (n + 1)
  let l := HomologicalComplex.homologyMap
    ((cechComplexFunctor (fun i => a ⁻¹ᵁ U i)).map e.hom) (n + 1)
  let eF := IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections
    (X := P.carrier) (fun i => a ⁻¹ᵁ U i) F (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) hF n
  let eG := IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections
    (X := P.carrier) (fun i => a ⁻¹ᵁ U i) G (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) hG n
  let q := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).map e
  have hn : l ≫ eG.hom = eF.hom ≫ q :=
    Cech.CohomologyNaturality.IntrinsicCech.cechHomologySuccIsoOfAcyclicIntersections_naturality
      (X := P.carrier) (fun i => a ⁻¹ᵁ U i) e
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) hF hG n
  change k ≫ (pG ≫ eG.hom) = (pF ≫ eF.hom) ≫ q
  calc
    k ≫ (pG ≫ eG.hom) = (k ≫ pG) ≫ eG.hom := (Category.assoc _ _ _).symm
    _ = (pF ≫ l) ≫ eG.hom := congrArg (fun v => v ≫ eG.hom) hi
    _ = pF ≫ (l ≫ eG.hom) := Category.assoc _ _ _
    _ = pF ≫ (eF.hom ≫ q) := congrArg (fun v => pF ≫ v) hn
    _ = (pF ≫ eF.hom) ≫ q := (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverCohomology
