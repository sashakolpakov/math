import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConcreteFiberCycleLifting
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FaithfulScalarExactness

/-! # Fiber Kernel Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberKernelBaseChange

noncomputable section

/-! The original model's differential kernel generates every cycle
after the actual scheme-fiber scalar extension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem actualFiber_native_kernel_baseChange_exact
    {X S : Scheme.{u}} [IsAffine S] [X.IsSeparated]
    (f : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (ha : ∀ i, IsAffineOpen (U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U) (x : S)
    [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
    [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]
    [Module.Finite Γ(S, ⊤) (D.X 2)] [Module.Projective Γ(S, ⊤) (D.X 2)]
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap (f.fiberι x) f (f.fiberToSpecResidueField x)
      (S.fromSpecResidueField x) (f.fiber_fac x) M U φ) 1]
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj M) 1)] :
    ((D.d 0 1).hom.shortComplexKer.map
      (ModuleCat.extendScalars (S.fromSpecResidueField x).appTop.hom)).Exact := by
  let A := S.presheaf.stalk x
  let : Algebra Γ(S, ⊤) A := (S.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let C := (D.d 0 1).hom.shortComplexKer
  have hi : (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex Γ(S, ⊤) A C)).Exact := by
    apply (ShortComplex.moduleCat_exact_iff_ker_sub_range _).mpr
    intro z hz
    exact ConcreteFiberCycleLifting.actualFiber_residue_cycle_mem_original_kernel_range f M U hU ha φ x z hz
  have hc : (C.map (ModuleCat.extendScalars (S.Γevaluation x).hom)).Exact :=
    (IteratedTensorExactness.iterated_tensor_exact_iff_composite (A := A) (B := IsLocalRing.ResidueField A) C).mp hi
  let a := (S.fromSpecResidueField x).appTop.hom
  let b := (Scheme.ΓSpecIso (S.residueField x)).hom.hom
  have he : b.comp a = (S.Γevaluation x).hom :=
    congrArg (fun q : Γ(S, ⊤) ⟶ S.residueField x => q.hom)
      (Quotients.FiniteDescent.FiberScalar.Construction.FiberScalarMaps.fromResidue_appTop S x)
  have hc' : (C.map (ModuleCat.extendScalars (b.comp a))).Exact := he.symm ▸ hc
  have ht : ((C.map (ModuleCat.extendScalars a)).map (ModuleCat.extendScalars b)).Exact :=
    (ShortComplex.exact_iff_of_iso (C.mapNatIso (ModuleCat.extendScalarsComp a b))).mp hc'
  exact (FaithfulScalarExactness.native_scalar_exact_iff_of_faithfullyFlat b
    (RingHom.FaithfullyFlat.of_bijective
      (Scheme.ΓSpecIso (S.residueField x)).commRingCatIsoToRingEquiv.bijective) _).mp ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberKernelBaseChange
