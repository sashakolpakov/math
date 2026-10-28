import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.CoefficientCechComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorExactness

/-! # Model Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelVanishing

noncomputable section

/-! Actual cohomology vanishing on a Cartesian Spec B fiber makes the B-linear base change of its finite model exact. Both the global-functions comparison and the change to B are explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem spec_model_exactAt_of_cohomology_zero
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    {B : Type u} [CommRing B] {P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {g : Spec (.of B) ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U)
    (ht : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M],
      QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map M φ))
    (n : ℕ) (hzero : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf (n + 1))) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapHomologicalComplex (.up ℕ)).obj C).ExactAt
      (n + 1) := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U ha he
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := quasiIso_comp _ _
  have hglobal : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) C).ExactAt (n + 1) :=
    Geometric.CechModelVanishing.geometric_model_exactAt_of_vanishing H L U hU ha φ n hzero
  let e : ModuleCat.of Γ(S, ⊤) B ≅ ModuleCat.of Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    (CoefficientCechComparison.specBaseCoefficientEquiv g).toLinearEquiv.toModuleIso
  let eC : HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex B C ≅ HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) C :=
    (Tensor.CochainBicomplex.tensorCochainFunctor C).mapIso e
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C (n + 1)).mpr (hglobal.of_iso eC.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelVanishing
