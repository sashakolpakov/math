import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ModuleTensorHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.ZariskiLinearity

/-! # External Factor Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomology

noncomputable section

/-! Genuine positive cohomology of a native external open factor is the tensor of parameter-chart sections with genuine cohomology on the proper factor. Every factor uses the same ambient inverse-image cover and the canonical pairing into its actual native sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable (U : Y.Opens) (hU : IsAffineOpen U)
variable (eU : (Scheme.Modules.pullback U.ι).obj N.sheaf ≅ Line.Bundles.structureModule U.toScheme)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (ha : ∀ i, IsAffineOpen (V i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))

def nativeExternalFactorCohomologyIso
    [Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))]
    (n : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)) ⋙
      HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom (n + 1)).obj L.sheaf) ≅
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) (n + 1)).obj
      ((IntrinsicCech.SheafComplex.cechFactorPresheaf (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj
        (op (b ⁻¹ᵁ U))) := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
  let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  let C := CoefficientCechComplex.coefficientCechComplex f.appTop.hom L.sheaf V
  let F := (IntrinsicCech.SheafComplex.cechFactorPresheaf
    (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj (op (b ⁻¹ᵁ U))
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : IsIso (AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V) :=
    AmbientCechTensor.nativeAmbientExternalCechTensorMap_isIso H L N.sheaf U hU eU V ha he
  exact T.mapIso (CoefficientCech.ZariskiLinearity.coefficientCechZariskiModuleIso f.appTop.hom L.sheaf V hV ha n).symm ≪≫
    ((C.sc (n + 1)).mapHomologyIso T).symm ≪≫
    HomologicalComplex.homologyMapIso (asIso
      (AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
        (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V)) (n + 1) ≪≫
    Additive.CommonCoverCohomology.additiveCommonCoverCohomologyIso a V hV F
      (ExternalFactorAcyclicity.nativeExternalFactor_commonCover_acyclic H L N U hU V ha) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomology
