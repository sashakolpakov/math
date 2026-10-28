import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.GeometricCechModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Cech Model Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing

noncomputable section

/-! Vanishing of actual positive fiber cohomology makes the tensored finite model exact in that degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem geometric_model_exactAt_of_vanishing
    {S X Y P : Scheme.{u}} [P.IsSeparated]
    {a : P ⟶ X} [IsAffineHom a] {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (q : ℕ)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      CechTensorComparison.geometricCechTensorMap H L.sheaf U) (q + 1)]
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf (q + 1))) :
    (Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra g) D).ExactAt (q + 1) := by
  let N : P.Modules := (L.pullback a).sheaf
  have : N.IsQuasicoherent := (L.pullback a).isQuasicoherent
  let c := a.appTop.hom.comp f.appTop.hom
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj N) := hH
  have hzero : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj N) :=
    ModuleCat.isZero_of_subsingleton _
  let K := Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N (fun i => a ⁻¹ᵁ U i)
  have hK : K.ExactAt (q + 1) := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology K (q + 1)).mpr
    exact (OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso c N (fun i => a ⁻¹ᵁ U i)
      (Affine.PushforwardZariskiComparison.inverseImageOpens_iSup_eq_top a U hU) (fun i => (ha i).preimage a) q).isZero_iff.mpr hzero
  exact (exactAt_iff_of_quasiIsoAt
    (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫ CechTensorComparison.geometricCechTensorMap H L.sheaf U)
      (q + 1)).mpr hK

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing
