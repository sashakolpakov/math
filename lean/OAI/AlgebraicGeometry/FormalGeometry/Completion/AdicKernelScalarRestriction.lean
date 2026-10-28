import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicAlgebraExactness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleReducedKernels

/-! # Adic Kernel Scalar Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernelScalarRestriction.Construction

noncomputable section

/-! Actual completed-kernel surjectivity is preserved under restricting scalars. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
  {M N : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[S] N)

/-- The kernel elements are unchanged by restriction of scalars. -/
def restrictedKernelEquiv : (f.restrictScalars R).ker ≃ₗ[R] f.ker where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem adicKernelMap_surjective_restrictScalars
    (h : Function.Surjective (AdicKernel.Construction.adicKernelMap (I.map (algebraMap R S)) f)) :
    Function.Surjective (AdicKernel.Construction.adicKernelMap I (f.restrictScalars R)) := by
  intro x
  have hx : AdicCompletion.map (I.map (algebraMap R S)) f
      (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M x.val) = 0 := by
    rw [← AdicAlgebraExactness.Construction.adicScalarRestrictionEquiv_naturality, x.property, map_zero]
  obtain ⟨y, hy⟩ := h ⟨_, hx⟩
  let z := (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I f.ker).symm y
  let w := (AdicCompletion.congr I (restrictedKernelEquiv (R := R) f)).symm z
  refine ⟨w, Subtype.ext ?_⟩
  apply (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M).injective
  have hw : AdicCompletion.map I (f.restrictScalars R).ker.subtype w =
      AdicCompletion.map I (f.ker.subtype.restrictScalars R) z := by
    change AdicCompletion.map I (f.restrictScalars R).ker.subtype
      (AdicCompletion.map I (restrictedKernelEquiv (R := R) f).symm.toLinearMap z) = _
    rw [AdicCompletion.map_comp_apply]
    rfl
  change AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I M
    (AdicCompletion.map I (f.restrictScalars R).ker.subtype w) = _
  rw [hw, AdicAlgebraExactness.Construction.adicScalarRestrictionEquiv_naturality]
  change AdicCompletion.map (I.map (algebraMap R S)) f.ker.subtype
    (AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I f.ker
      ((AdicScalarRestriction.Construction.adicScalarRestrictionEquiv (S := S) I f.ker).symm y)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val hy

/-- The literal reduced-kernel comparison stays surjective over the original coefficient ring. -/
theorem reducedKernelComparison_surjective_restrictScalars
    (h : Function.Surjective (CompatibleReducedKernels.Construction.reducedKernelComparison (I.map (algebraMap R S)) f)) :
    Function.Surjective (CompatibleReducedKernels.Construction.reducedKernelComparison I (f.restrictScalars R)) := by
  have hs : Function.Surjective (AdicKernel.Construction.adicKernelMap (I.map (algebraMap R S)) f) := by
    intro x
    obtain ⟨y, hy⟩ := h (CompatibleReducedKernels.Construction.completedKernelCompatibleEquiv (I.map (algebraMap R S)) f x)
    exact ⟨y, (CompatibleReducedKernels.Construction.completedKernelCompatibleEquiv (I.map (algebraMap R S)) f).injective hy⟩
  exact (CompatibleReducedKernels.Construction.completedKernelCompatibleEquiv I (f.restrictScalars R)).surjective.comp
    (adicKernelMap_surjective_restrictScalars I f hs)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernelScalarRestriction.Construction
