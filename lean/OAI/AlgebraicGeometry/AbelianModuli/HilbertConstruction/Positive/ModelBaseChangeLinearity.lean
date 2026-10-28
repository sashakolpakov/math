import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeHomologyScalarCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.CoverPushforwardCohomology

/-! # Model Base Change Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ModelBaseChangeLinearity

noncomputable section

/-! A genuine positive-degree Cech model computes cohomology linearly over
an arbitrary coefficient algebra. Linearity follows from the actual scalar
endomorphisms, with no surjectivity condition on the coefficient map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

def positiveCechModelBaseChangeLinearEquiv
    (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => a ⁻¹ᵁ U i)
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback a).obj M)))
    {C : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
    (n : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U) (n + 1)] :
    ((((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology (n + 1)) ≃ₗ[B]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor q (n + 1)).obj ((Scheme.Modules.pullback a).obj M)) := by
  let N := (Scheme.Modules.pullback a).obj M
  let ψ := Module.TensorFunctor.ModuleTensorFunctor.map B φ ≫ Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap a c M q hq U
  let eT := Base.ChangeTensorHomology.baseChangeTensorHomologyIso (B := B) C (n + 1)
  let eψ := asIso (HomologicalComplex.homologyMap ψ (n + 1))
  let eH := Common.CoverPushforwardCohomology.commonCoverPushforwardCohomologyModuleIso a c U hU N hM n
  let e := (eT ≪≫ eψ ≪≫ eH).toLinearEquiv.toAddEquiv
  refine { e with map_smul' := ?_ }
  intro b x
  let t := Tensor.CochainBicomplex.tensorCochainMap C (ModuleCat.ofHom (Cech.TensorScalarLinearity.coefficientAlgebraMultiplication (R := R) b))
  let s := Global.ModuleScalars.globalModuleScalar N (q b)
  let d := (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map ((Scheme.Modules.pushforward a).map s)
  have hm : HomologicalComplex.homologyMap ψ (n + 1) ≫ HomologicalComplex.homologyMap d (n + 1) =
      HomologicalComplex.homologyMap t (n + 1) ≫ HomologicalComplex.homologyMap ψ (n + 1) := by
    have h := congrArg (fun k => HomologicalComplex.homologyMap k (n + 1))
      (Cech.TensorScalarLinearity.coefficientCechModel_scalar a c M q hq U b φ)
    change HomologicalComplex.homologyMap (ψ ≫ d) (n + 1) =
      HomologicalComplex.homologyMap (t ≫ ψ) (n + 1) at h
    rw [HomologicalComplex.homologyMap_comp ψ d, HomologicalComplex.homologyMap_comp t ψ] at h
    exact h
  have hh : HomologicalComplex.homologyMap d (n + 1) ≫ eH.hom =
      eH.hom ≫ (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (a.appTop.hom.comp c) (n + 1)).map s :=
    Common.CoverPushforwardCohomology.commonCoverPushforwardCohomologyModuleIso_naturality a c U hU s hM hM n
  change eH.hom (eψ.hom (eT.hom (b • x))) =
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (a.appTop.hom.comp c) (n + 1)).map s
      (eH.hom (eψ.hom (eT.hom x)))
  rw [Base.ChangeHomologyScalarCompatibility.baseChangeTensorHomologyIso_smul]
  calc
    _ = eH.hom (HomologicalComplex.homologyMap d (n + 1) (eψ.hom (eT.hom x))) :=
      congrArg eH.hom (ConcreteCategory.congr_hom hm (eT.hom x)).symm
    _ = _ := ConcreteCategory.congr_hom hh (eψ.hom (eT.hom x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ModelBaseChangeLinearity
