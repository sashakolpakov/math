import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarExactness

/-! # Fiber Model Intrinsic Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelIntrinsicExactness

noncomputable section

/-! Actual first fiber cohomology vanishing gives degree-one exactness of the native scalar extension of the finite cochain model. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem fiber_model_native_exact_of_H1_vanishing
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated] (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, IsAffineOpen (U i)) {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (x : S)
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf U) 1]
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1 := by
  have : IsAffineHom (S.fromSpecResidueField x) := isAffineHom_of_isAffine _
  have : IsAffineHom (pullback.fst f (S.fromSpecResidueField x)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField x)).flip inferInstance
  have : (pullback f (S.fromSpecResidueField x)).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.fst f (S.fromSpecResidueField x))]; infer_instance⟩
  have ht := Geometric.CechModelVanishing.geometric_model_exactAt_of_vanishing
    (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L U hU ha φ 0 hH
  exact (Tensor.ScalarExactness.tensor_exactAt_iff_native (S.fromSpecResidueField x).appTop.hom D 1).mp ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelIntrinsicExactness
