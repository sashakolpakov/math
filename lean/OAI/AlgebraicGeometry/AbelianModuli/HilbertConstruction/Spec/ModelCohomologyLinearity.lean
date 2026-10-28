import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelAllDegreeVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence

/-! # Model Cohomology Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelCohomologyLinearity

noncomputable section

/-! A universal finite Cech model computes actual sheaf cohomology on a Spec B fiber, linearly over B whenever the coefficient map is surjective. The comparison includes every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def specModelCohomologyLinearEquiv
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
    (hs : Function.Surjective (CoefficientCechComparison.specBaseCoefficientMap g)) (q : ℕ) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapHomologicalComplex (.up ℕ)).obj C).homology q) ≃ₗ[B]
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (CoefficientCechComparison.specPullbackCoefficientMap (b := b)) q).obj
        (L.pullback a).sheaf) := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
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
  exact Base.ChangeTensorHomology.restrictedModuleIsoLinearEquiv (algebraMap R B) hs eR

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelCohomologyLinearity
