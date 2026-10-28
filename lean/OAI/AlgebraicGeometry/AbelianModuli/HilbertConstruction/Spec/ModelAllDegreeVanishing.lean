import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

/-! # Model All Degree Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelAllDegreeVanishing

noncomputable section

/-! The actual Spec B fiber comparison transfers cohomology vanishing to the B-linear model in every degree, including degree zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem geometric_model_exactAt_of_cohomology_zero_all
    {S X Y P : Scheme.{u}} [P.IsSeparated]
    {a : P ⟶ X} [IsAffineHom a] {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (q : ℕ)
    [QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫ Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) q]
    (hzero : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q)) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) C).ExactAt q := by
  let N : P.Modules := (L.pullback a).sheaf
  have : N.IsQuasicoherent := (L.pullback a).isQuasicoherent
  let c := a.appTop.hom.comp f.appTop.hom
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj N) := hzero
  have hz : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj N) :=
    ModuleCat.isZero_of_subsingleton _
  let T := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N (fun i => a ⁻¹ᵁ U i)
  have hT : T.ExactAt q := by
    apply (T.exactAt_iff_isZero_homology q).mpr
    exact (OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso c N (fun i => a ⁻¹ᵁ U i)
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) (fun i => (ha i).preimage a) q).isZero_iff.mpr hz
  exact (exactAt_iff_of_quasiIsoAt
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫ Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) q).mpr hT

theorem spec_model_exactAt_of_cohomology_zero_all
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
    (q : ℕ) (hzero : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q)) :
    let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra;
    (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(S, ⊤) B).mapHomologicalComplex (.up ℕ)).obj C).ExactAt q := by
  let : Algebra Γ(S, ⊤) B := (CoefficientCechComparison.specBaseCoefficientMap g).toAlgebra
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom a := isAffineHom_isStableUnderBaseChange.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ) := ht (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
  have : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := Framed.AffineCechTensorIsomorphism.geometricCechTensorMap_isIso H L U ha he
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫ Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) :=
    quasiIso_comp _ _
  have hglobal := geometric_model_exactAt_of_cohomology_zero_all H L U hU ha φ q hzero
  let e : ModuleCat.of Γ(S, ⊤) B ≅ ModuleCat.of Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    (CoefficientCechComparison.specBaseCoefficientEquiv g).toLinearEquiv.toModuleIso
  let eC := (Tensor.CochainBicomplex.tensorCochainFunctor C).mapIso e
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C q).mpr (hglobal.of_iso eC.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelAllDegreeVanishing
