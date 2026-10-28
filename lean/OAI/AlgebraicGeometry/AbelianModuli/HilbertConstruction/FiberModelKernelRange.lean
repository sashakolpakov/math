import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechModelVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarExactness

/-! # Fiber Model Kernel Range -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelKernelRange

noncomputable section

/-! Actual first fiber cohomology vanishing gives the original finite model's tensor-kernel range condition at that fiber. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem fiber_model_kernel_range_of_H1_vanishing
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, IsAffineOpen (U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (x : S)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    [QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf U) 1]
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    ((D.d 0 1).hom.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))).ker ≤
      ((D.d 0 1).hom.ker.subtype.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))).range := by
  have hbase : IsAffineHom (S.fromSpecResidueField x) :=
    isAffineHom_of_isAffine (S.fromSpecResidueField x)
  have hstable : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) => IsAffineHom g) :=
    isAffineHom_isStableUnderBaseChange
  have hfa : IsAffineHom (pullback.fst f (S.fromSpecResidueField x)) :=
    hstable.of_isPullback (IsPullback.of_hasPullback f (S.fromSpecResidueField x)).flip hbase
  have : IsAffineHom (f.fiberι x) := hfa
  have hpsep : (pullback f (S.fromSpecResidueField x)).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.fst f (S.fromSpecResidueField x))]; infer_instance⟩
  have : (f.fiber x).IsSeparated := hpsep
  have ht : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) D).ExactAt 1 :=
    Geometric.CechModelVanishing.geometric_model_exactAt_of_vanishing (IsPullback.of_hasPullback f (S.fromSpecResidueField x))
      L U hU ha φ 0 hH
  have hn : (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1 :=
    (Tensor.ScalarExactness.tensor_exactAt_iff_native (S.fromSpecResidueField x).appTop.hom D 1).mp ht
  exact Tensor.KernelScalarExactness.tensor_kernel_range_of_native_exact (S.fromSpecResidueField x).appTop.hom (D.d 0 1)
    (FiberKernelExactness.fiber_native_kernel_exact_of_degree_one_exact S x D hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelKernelRange
