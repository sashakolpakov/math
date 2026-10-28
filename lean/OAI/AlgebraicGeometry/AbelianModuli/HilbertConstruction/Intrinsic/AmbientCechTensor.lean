import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientAffinePairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism

/-! # Ambient Cech Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechTensor

noncomputable section

/-! On a finite affine frame cover of the proper factor, the native ambient pairing identifies the actual Cech cochain complex with the tensor of the coefficient Cech complex by parameter-chart sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u

private theorem isIso_iso_hom_comp_cochain
    {K L M : CochainComplex AddCommGrpCat.{u} ℕ} (e : K ≅ L)
    (a : L ⟶ M) (ha : IsIso a) : IsIso (e.hom ≫ a) := by
  have : IsIso a := ha
  infer_instance

variable {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY) (M : X.Modules) (N : Y.Modules)
variable (U : Y.Opens) {ι : Type u} [Finite ι] (V : ι → X.Opens)

def nativeAmbientExternalCechTensorMap :
    ((Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) ⋙ Module.ProductForget.moduleForget R).mapHomologicalComplex
      (.up ℕ)).obj (CoefficientCechComplex.coefficientCechComplex cX M V) ⟶
    (cechComplexFunctor V).obj (AmbientOpenFactorSections.ambientOpenFactorSectionPresheaf a (b ⁻¹ᵁ U)
      (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
        ((Scheme.Modules.pullback b).obj N)))) :=
  (HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso
    (Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U)) ⋙ Module.ProductForget.moduleForget R)
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M) V).hom ≫
    (cechComplexFunctor V).map
      ((Functor.associator (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M)
        (Module.TensorFunctor.ModuleTensorFunctor.tensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op U))) (Module.ProductForget.moduleForget R)).inv ≫
          AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U)

theorem nativeAmbientExternalCechTensorMap_isIso
    {S X Y P : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Y.Modules)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (eU : (Scheme.Modules.pullback U.ι).obj N ≅ Line.Bundles.structureModule U.toScheme)
    {ι : Type u} [Finite ι] (V : ι → X.Opens) (ha : ∀ i, IsAffineOpen (V i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme)) :
    IsIso (nativeAmbientExternalCechTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N U V) := by
  let A := (Coefficient.ModulePresheaf.coefficientModulePresheaf g.appTop.hom N).obj (op U)
  let α := (Functor.associator (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf)
      (Module.TensorFunctor.ModuleTensorFunctor.tensor A) (Module.ProductForget.moduleForget Γ(S, ⊤))).inv ≫
    AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N U
  have hα : IsIso ((cechComplexFunctor V).map α) := by
    apply HilbertConstruction.Finite.CechFunctorComparison.cechComplex_map_isIso_of_intersections V α
    intro n i
    let W : X.Opens := ∏ᶜ fun k : Fin (n + 1) => V (i k)
    have hW : IsAffineOpen W := Affine.CechIntersections.affine_cechIntersection V ha n i
    have hle : W ≤ V (i 0) := leOfHom (Pi.π (fun k : Fin (n + 1) => V (i k)) 0)
    have : IsIso ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N U).app (op W)) :=
      AmbientAffinePairing.affineFrames_nativeAmbientExternalSectionMap_isIso H L.sheaf N W U hW hU
        (L.frameRestrict hle (he (i 0)).some) eU
    change IsIso ((_ ≫ AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N U).app (op W))
    rw [NatTrans.comp_app]
    infer_instance
  exact isIso_iso_hom_comp_cochain
    (HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso
      (Module.TensorFunctor.ModuleTensorFunctor.tensor (R := Γ(S, ⊤)) A ⋙ Module.ProductForget.moduleForget Γ(S, ⊤))
      (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf) V)
    ((cechComplexFunctor V).map α) hα

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientCechTensor
