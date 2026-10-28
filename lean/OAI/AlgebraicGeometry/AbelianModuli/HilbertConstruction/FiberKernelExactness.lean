import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberResidueModelExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.KernelBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulScalarExactness

/-! # Fiber Kernel Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelExactness

noncomputable section

/-! Degree-one exactness of the actual fiber scalar extension makes the original differential-kernel sequence exact after that scalar extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem fiber_native_kernel_exact_of_degree_one_exact
    (S : Scheme.{u}) [IsAffine S] (x : S)
    (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    (h : (((ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom).mapHomologicalComplex
      (.up ℕ)).obj D).ExactAt 1) :
    ((D.d 0 1).hom.shortComplexKer.map
      (ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom)).Exact := by
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) A := FiberScalar.FiberScalarMaps.stalk_flat S x
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 0))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₁ :=
    inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 0))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 1))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₂ :=
    inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 1))
  have : Module.Finite Γ(S, ⊤) (D.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Finite Γ(S, ⊤) (D.X 2))
  have : Module.Projective Γ(S, ⊤) (D.sc' 0 1 2).X₃ :=
    inferInstanceAs (Module.Projective Γ(S, ⊤) (D.X 2))
  let C := (D.d 0 1).hom.shortComplexKer
  have hi : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) A C)).Exact := by
    apply (ShortComplex.moduleCat_exact_iff_ker_sub_range _).mpr
    intro z hz
    exact Residue.KernelBaseChange.residue_cycle_mem_original_kernel_range (D.sc' 0 1 2)
      (FiberResidueModelExactness.fiber_model_residue_exact S x D h) z hz
  have hc : (C.map (ModuleCat.extendScalars (S.Γevaluation x).hom)).Exact :=
    (Iterated.TensorExactness.iterated_tensor_exact_iff_composite (A := A) (B := IsLocalRing.ResidueField A) C).mp hi
  let a := (S.fromSpecResidueField x).appTop.hom
  let b := (Scheme.ΓSpecIso (S.residueField x)).hom.hom
  have he : b.comp a = (S.Γevaluation x).hom :=
    congrArg (fun q : Γ(S, ⊤) ⟶ S.residueField x => q.hom) (FiberScalar.FiberScalarMaps.fromResidue_appTop S x)
  have hc' : (C.map (ModuleCat.extendScalars (b.comp a))).Exact := he.symm ▸ hc
  have ht : ((C.map (ModuleCat.extendScalars a)).map (ModuleCat.extendScalars b)).Exact :=
    (ShortComplex.exact_iff_of_iso (C.mapNatIso (ModuleCat.extendScalarsComp a b))).mp hc'
  exact (FaithfulScalarExactness.native_scalar_exact_iff_of_faithfullyFlat b
    (RingHom.FaithfullyFlat.of_bijective
      (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.bijective) _).mp ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberKernelExactness
