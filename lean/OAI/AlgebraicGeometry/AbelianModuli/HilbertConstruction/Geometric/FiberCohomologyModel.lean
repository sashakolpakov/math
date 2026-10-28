import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.TensorHomologyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ResidueScalar
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing

/-! # Fiber Cohomology Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberCohomologyModel

noncomputable section

/-! The native residue-field extension of the finite Cech model computes genuine fiber cohomology with the full residue-field coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def fiberModelCohomologyIso
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated] (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, IsAffineOpen (U i)) {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (x : S) (q : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      CechTensorComparison.geometricCechTensorMap (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf U) q] :
    (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).homology q ≅
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (f.fiberToSpecResidueField x).appTop.hom q).obj
          (L.pullback (f.fiberι x)).sheaf := by
  let g := S.fromSpecResidueField x
  let H := IsPullback.of_hasPullback f g
  let a := pullback.fst f g
  let b := pullback.snd f g
  let M := (L.pullback a).sheaf
  have : M.IsQuasicoherent := (L.pullback a).isQuasicoherent
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : (pullback f g).IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  apply Affine.ResidueScalar.affineResidueModuleIso S x
  exact Intrinsic.TensorHomologyComparison.nativeTensorHomologyComparisonIso g.appTop.hom D q ≪≫
    isoOfQuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorMap H L.sheaf U) q ≪≫
    OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso (a.appTop.hom.comp f.appTop.hom) M
      (fun i => a ⁻¹ᵁ U i) (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) (fun i => (ha i).preimage a) q ≪≫
    CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M q ≪≫
    (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso g.appTop.hom b.appTop.hom M q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiberCohomologyModel
