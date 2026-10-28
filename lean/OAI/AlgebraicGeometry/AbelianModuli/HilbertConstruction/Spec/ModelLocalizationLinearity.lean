import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelCohomologyLinearity
import Mathlib.RingTheory.Localization.Module

/-! # Model Localization Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelLocalizationLinearity

noncomputable section

/-! The geometric cohomology comparison is linear over a localized coefficient ring. Localization makes every map that is linear over the original ring linear over the new ring as well. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def restrictedModuleIsoLinearEquivOfLocalization
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (s : Submonoid R) [IsLocalization s B] {M N : ModuleCat.{u} B}
    (e : (ModuleCat.restrictScalars (algebraMap R B)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj N) : M ≃ₗ[B] N := by
  letI : Module R M := Module.compHom M (algebraMap R B)
  letI : Module R N := Module.compHom N (algebraMap R B)
  letI : IsScalarTower R B M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let er : M ≃ₗ[R] N := {
    toFun := fun x => e.hom x
    invFun := fun y => e.inv y
    left_inv := e.toLinearEquiv.left_inv
    right_inv := e.toLinearEquiv.right_inv
    map_add' := e.toLinearEquiv.map_add
    map_smul' := e.toLinearEquiv.map_smul }
  exact er.extendScalarsOfIsLocalization s B

def specModelCohomologyLinearEquivOfLocalization
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {B : Type u} [CommRing B] {P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {g : Spec (.of B) ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
    (ht : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map M φ))
    (s : Submonoid Γ(S, ⊤))
    (hloc : let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra; IsLocalization s B)
    (q : ℕ) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapHomologicalComplex (.up ℕ)).obj C).homology q) ≃ₗ[B]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) q).obj
        (L.pullback a).sheaf) := by
  letI : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  letI : IsLocalization s B := hloc
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  let R := Γ(S, ⊤)
  let N : P.Modules := (L.pullback a).sheaf
  have : N.IsQuasicoherent := (L.pullback a).isQuasicoherent
  let cR := a.appTop.hom.comp f.appTop.hom
  let cB := CoefficientCechComparison.specPullbackCoefficientMap (b := b)
  let CB := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C
  let ψ := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫ Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U ha he
  have : QuasiIso ψ := quasiIso_comp _ _
  let e : ModuleCat.of R B ≅ ModuleCat.of R (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    (CoefficientCechComparison.specBaseCoefficientEquiv g).toLinearEquiv.toModuleIso
  let eC := (Tensor.CochainBicomplex.tensorCochainFunctor C).mapIso e
  have : QuasiIsoAt ψ q := inferInstance
  have : IsIso (HomologicalComplex.homologyMap ψ q) := inferInstance
  let eψ := asIso (HomologicalComplex.homologyMap ψ q)
  let eR : (ModuleCat.restrictScalars (algebraMap R B)).obj (CB.homology q) ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor cB q).obj N) :=
    Base.ChangeTensorHomology.baseChangeTensorHomologyIso C q ≪≫ HomologicalComplex.homologyMapIso eC q ≪≫
      eψ ≪≫
      OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso cR N (fun i => a ⁻¹ᵁ U i)
        (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) (fun i => (ha i).preimage a) q ≪≫
      (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr (CoefficientCechComparison.specPullbackCoefficient_compatible H) N q).symm ≪≫
      (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso (algebraMap R B) cB N q).symm
  exact restrictedModuleIsoLinearEquivOfLocalization s eR

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelLocalizationLinearity
