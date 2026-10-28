import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberFlatCriterion
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Local Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalFlatness.Construction

noncomputable section

/-! The finite-module fiberwise flatness criterion for the Openness proof. -/

open IsLocalRing TensorProduct _root_.Module
open scoped TensorProduct

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [IsLocalRing R]

/-- The algebraic fiber can be computed either by tensoring the base ring
and then the module, or by tensoring the module directly. -/
def residueFiberEquiv
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    (A ⊗[R] ResidueField R) ⊗[A] M ≃ₗ[R] ResidueField R ⊗[R] M :=
  (TensorProduct.comm A (A ⊗[R] ResidueField R) M).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A A M (ResidueField R)).restrictScalars R ≪≫ₗ
    TensorProduct.comm R M (ResidueField R)

theorem residueFiberEquiv_tmul
    {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (a : A) (k : ResidueField R) (m : M) :
    residueFiberEquiv R A M ((a ⊗ₜ[R] k) ⊗ₜ[A] m) = k ⊗ₜ[R] (a • m) := by
  simp [residueFiberEquiv]

theorem residueFiberEquiv_natural
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[A] N) :
    (f.restrictScalars R).lTensor (ResidueField R) ∘ₗ
        (residueFiberEquiv R A M).toLinearMap =
      (residueFiberEquiv R A N).toLinearMap ∘ₗ
        ((f.baseChange (A ⊗[R] ResidueField R)).restrictScalars R) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul c m =>
    induction c using TensorProduct.inductionOn with
    | add c d hc hd =>
      simpa only [add_tmul, map_add] using congrArg₂ (· + ·) hc hd
    | tmul a k => simp [residueFiberEquiv_tmul]

/-- The finite-module fiberwise flatness criterion for a local algebra:
base-flatness and flatness of the closed fiber imply flatness over the algebra. -/
theorem flat_of_flat_residueField_fiber
    [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.FinitePresentation A N] [Module.Flat R N]
    [Module.Flat (A ⊗[R] ResidueField R) ((A ⊗[R] ResidueField R) ⊗[A] N)] :
    Module.Flat A N := by
  let C := A ⊗[R] ResidueField R
  let φ : C →ₐ[R] ResidueField A :=
    Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R A (ResidueField A))
      (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A))
      (fun _ _ => Commute.all _ _)
  have : Nontrivial C := φ.toRingHom.domain_nontrivial
  have hC : Function.Surjective (algebraMap A C) :=
    Algebra.TensorProduct.includeLeft_surjective A A (residue_surjective (R := R))
  have : IsLocalRing C := IsLocalRing.of_surjective' (algebraMap A C) hC
  have : Module.Finite C (C ⊗[A] N) := inferInstance
  have : Module.Flat C (C ⊗[A] N) := inferInstance
  have : Module.Free C (C ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  let ι := Module.Free.ChooseBasisIndex C (C ⊗[A] N)
  let b : Basis ι C (C ⊗[A] N) := Module.Free.chooseBasis C (C ⊗[A] N)
  have : Finite ι := Module.Finite.finite_basis b
  have hmk := TensorProduct.mk_surjective A N C hC
  choose v hv using fun i : ι => hmk (b i)
  let f : (ι →₀ A) →ₗ[A] N := Finsupp.linearCombination A v
  let bsrc : Basis ι C (C ⊗[A] (ι →₀ A)) :=
    (Finsupp.basisSingleOne (R := A) (ι := ι)).baseChange C
  let eC : (C ⊗[A] (ι →₀ A)) ≃ₗ[C] (C ⊗[A] N) :=
    bsrc.repr ≪≫ₗ b.repr.symm
  have heC : f.baseChange C = eC.toLinearMap := by
    apply bsrc.ext
    intro i
    change (f.baseChange C) (bsrc i) = eC (bsrc i)
    calc
      (f.baseChange C) (bsrc i) = b i := by
        simpa only [bsrc, Basis.baseChange_apply, Finsupp.coe_basisSingleOne,
          LinearMap.baseChange_tmul, f, Finsupp.linearCombination_single,
          one_smul, TensorProduct.mk_apply] using hv i
      _ = eC (bsrc i) := by simp [eC]
  let eR : (ResidueField R ⊗[R] (ι →₀ A)) ≃ₗ[R] (ResidueField R ⊗[R] N) :=
    (residueFiberEquiv R A (ι →₀ A)).symm ≪≫ₗ
      eC.restrictScalars R ≪≫ₗ residueFiberEquiv R A N
  have heR : (f.restrictScalars R).lTensor (ResidueField R) = eR.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := (residueFiberEquiv R A (ι →₀ A)).surjective x
    have hn := LinearMap.congr_fun (residueFiberEquiv_natural R A f) z
    have heC' : f.baseChange (A ⊗[R] ResidueField R) = eC.toLinearMap := heC
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hn
    rw [heC'] at hn
    simpa [eR] using hn
  apply FiberFlatCriterion.Construction.flat_of_flat_source_of_residueField_tensor_iso (R := R) f
  rw [heR]
  exact eR.bijective

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalFlatness.Construction
