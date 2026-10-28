import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.TensorKernelInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberModelIntrinsicExactness

/-! # Fiber Kernel Tensor Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelTensorInjection

noncomputable section

/-! Vanishing of first fiber cohomology makes the canonical tensor map of the original degree-zero kernel injective. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem fiber_native_kernel_mono_of_degree_one_exact
    (S : Scheme.{u}) [IsAffine S] (x : S)
    (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    (h : (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1) :
    Mono ((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).map
      (ModuleCat.ofHom (D.d 0 1).hom.ker.subtype)) := by
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) A := FiberScalar.FiberScalarMaps.stalk_flat S x
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₁ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₂ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₃ := inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 2))
  let i : ModuleCat.of Γ(S, ⊤) (D.d 0 1).hom.ker ⟶ D.X 0 := ModuleCat.ofHom (D.d 0 1).hom.ker.subtype
  have hi := Residue.TensorKernelInjection.iterated_tensor_original_kernel_injective (B := IsLocalRing.ResidueField A) (D.sc' 0 1 2)
    (FiberResidueModelExactness.fiber_model_residue_exact S x D h)
  have hc : Mono ((ModuleCat.extendScalars (S.Γevaluation x).hom).map i) :=
    (Scalar.Monomorphisms.native_iterated_scalar_mono_iff (A := A) (B := IsLocalRing.ResidueField A) i).mpr hi
  let a := (S.fromSpecResidueField x).appTop.hom
  let b := (Scheme.ΓSpecIso (S.residueField x)).hom.hom
  have he : b.comp a = (S.Γevaluation x).hom :=
    congrArg (fun q : Γ(S, ⊤) ⟶ S.residueField x => q.hom) (FiberScalar.FiberScalarMaps.fromResidue_appTop S x)
  have hc' : Mono ((ModuleCat.extendScalars (b.comp a)).map i) := he.symm ▸ hc
  have ht : Mono ((ModuleCat.extendScalars b).map ((ModuleCat.extendScalars a).map i)) :=
    (Scalar.Monomorphisms.mono_map_iff_of_functor_iso (ModuleCat.extendScalarsComp a b) i).mp hc'
  exact (Scalar.Monomorphisms.native_scalar_mono_iff_of_faithfullyFlat b
    (RingHom.FaithfullyFlat.of_bijective (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.bijective)
    ((ModuleCat.extendScalars a).map i)).mp ht

theorem fiber_model_kernel_tensor_injective_of_H1_vanishing
    {S X : Scheme.{u}} [IsAffine S] [X.IsSeparated] (f : X ⟶ S) (L : Line.Bundles.LineBundle X)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ i, IsAffineOpen (U i)) {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U) (x : S)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    [QuasiIsoAt (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x)) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorMap (IsPullback.of_hasPullback f (S.fromSpecResidueField x)) L.sheaf U) 1]
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1)) :
    Function.Injective ((D.d 0 1).hom.ker.subtype.lTensor (Affine.TensorSectionComparison.morphismGlobalAlgebra (S.fromSpecResidueField x))) := by
  have hn := FiberModelIntrinsicExactness.fiber_model_native_exact_of_H1_vanishing f L U hU ha φ x hH
  have hi := fiber_native_kernel_mono_of_degree_one_exact S x D hn
  exact Tensor.KernelScalarInjection.tensor_kernel_injective_of_native_mono (S.fromSpecResidueField x).appTop.hom (D.d 0 1) hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelTensorInjection
