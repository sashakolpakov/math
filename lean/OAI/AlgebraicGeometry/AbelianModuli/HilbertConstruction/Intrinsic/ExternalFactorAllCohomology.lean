import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CommonCoverDegreeZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroLinearity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero

/-! # External Factor All Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAllCohomology

noncomputable section

/-! The native external-factor cohomology formula includes degree zero. Thus lower-degree vanishing of the proper-factor line bundle transfers to every actual open factor of the product Cech resolution. -/
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
variable [hflat : Module.Flat Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U))]

def nativeExternalFactorAllCohomologyIso (n : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)) ⋙
      HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf) ≅
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology P) n).obj
      ((IntrinsicCech.SheafComplex.cechFactorPresheaf (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj
        (op (b ⁻¹ᵁ U))) := by
  cases n with
  | zero =>
      let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)
      let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A ⋙ HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
      let C := CoefficientCechComplex.coefficientCechComplex f.appTop.hom L.sheaf V
      let F := (IntrinsicCech.SheafComplex.cechFactorPresheaf
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj (op (b ⁻¹ᵁ U))
      have : IsIso (AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
          (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V) :=
        AmbientCechTensor.nativeAmbientExternalCechTensorMap_isIso H L N.sheaf U hU eU V ha he
      exact T.mapIso ((CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv f.appTop.hom L.sheaf).toModuleIso ≪≫
          CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso f.appTop.hom L.sheaf V hV) ≪≫
        ((C.sc 0).mapHomologyIso T).symm ≪≫
        HomologicalComplex.homologyMapIso (asIso
          (AmbientCechTensor.nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
            (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N.sheaf U V)) 0 ≪≫
        Additive.CommonCoverDegreeZero.additiveCommonCoverZeroCohomologyIso a V hV F
  | succ n => exact ExternalFactorCohomology.nativeExternalFactorCohomologyIso H L N U hU eU V hV ha he n

include H hU eU V hV ha he hflat in
theorem nativeExternalFactor_cohomology_vanish (n : ℕ)
    (hL : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf n)) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((IntrinsicCech.SheafComplex.cechFactorPresheaf (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (((L.pullback a).tensor (N.pullback b)).sheaf))).obj
        (op (b ⁻¹ᵁ U))) n) := by
  let : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf) := hL
  let T := HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N.sheaf).obj (op U)) ⋙
    HilbertConstruction.Module.ProductForget.moduleForget Γ(S, ⊤)
  have hz := T.map_isZero (ModuleCat.isZero_of_subsingleton
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom n).obj L.sheaf))
  exact AddCommGrpCat.subsingleton_of_isZero
    ((nativeExternalFactorAllCohomologyIso H L N U hU eU V hV ha he n).isZero_iff.mp hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ExternalFactorAllCohomology
