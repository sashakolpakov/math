import OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainReducedKernels

/-! # Finite Model Completion -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.FiniteModelCompletion.Construction

noncomputable section

/-!
# Completion: formal zero-cycles for a universally valid finite cochain model

The completion comparison uses the actual kernel inclusion. Its
surjectivity follows from a finite model and the actual quotient cochain
maps, without assuming that the original cochain terms are finite modules.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)

/-- The canonical formal zero-cycle comparison, packaged with its actual cochain complex. -/
def cochainFormalZeroCycleComparison (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    AdicCompletion I (C.d 0 1).hom.ker →ₗ[R] CompatibleReducedKernels.Construction.compatibleReducedKernels I (C.d 0 1).hom :=
  CompatibleReducedKernels.Construction.reducedKernelComparison I (C.d 0 1).hom

/-- Surjectivity of the actual canonical cochain comparison. This abbreviation of the
proposition keeps elaboration from unfolding large geometric cochain terms. -/
def FormalZeroCycleComparisonSurjective (C : CochainComplex (ModuleCat.{u} R) ℕ) : Prop :=
  Function.Surjective (cochainFormalZeroCycleComparison I C)

/-- Completion and reduction of actual zero-cycles commute with the cochain map. -/
theorem reducedKernelComparison_naturality (x : AdicCompletion I (C.d 0 1).hom.ker) :
    CompatibleReducedKernels.Construction.reducedKernelComparison I (D.d 0 1).hom (AdicCompletion.map I (CochainReducedKernels.Construction.cochainKernelMap φ) x) =
      CochainReducedKernels.Construction.compatibleReducedCochainMap φ I (CompatibleReducedKernels.Construction.reducedKernelComparison I (C.d 0 1).hom x) := by
  apply Subtype.ext
  funext n
  change (AdicCompletion.map I (D.d 0 1).hom.ker.subtype
      (AdicCompletion.map I (CochainReducedKernels.Construction.cochainKernelMap φ) x)).val n =
    (AdicCompletion.map I (φ.f 0).hom
      (AdicCompletion.map I (C.d 0 1).hom.ker.subtype x)).val n
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  rfl

/-- A finite model which computes reduced degree-zero cohomology gives surjectivity. -/
theorem reducedKernelComparison_surjective_of_finite_model [IsNoetherianRing R]
    [Module.Finite R (C.X 0)] [Module.Finite R (C.X 1)]
    [∀ n, QuasiIsoAt (AdicReduction.Construction.adicReductionMap (I ^ n) φ) 0] :
    Function.Surjective (CompatibleReducedKernels.Construction.reducedKernelComparison I (D.d 0 1).hom) := by
  intro x
  obtain ⟨y, hy⟩ := (CochainReducedKernels.Construction.compatibleReducedCochainMap_bijective φ I).surjective x
  obtain ⟨z, hz⟩ := (CompatibleReducedKernels.Construction.reducedKernelComparison_bijective I (C.d 0 1).hom).surjective y
  refine ⟨AdicCompletion.map I (CochainReducedKernels.Construction.cochainKernelMap φ) z, ?_⟩
  rw [reducedKernelComparison_naturality, hz, hy]

/-- A model valid after arbitrary scalar tensor computes formal degree-zero cohomology. -/
theorem reducedKernelComparison_surjective_of_tensor_finite_model [IsNoetherianRing R]
    [Module.Finite R (C.X 0)] [Module.Finite R (C.X 1)]
    (hφ : ∀ n, QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I ^ n) φ)) :
    Function.Surjective (CompatibleReducedKernels.Construction.reducedKernelComparison I (D.d 0 1).hom) := by
  let (n : ℕ) : QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I ^ n) φ) := hφ n
  let (n : ℕ) : QuasiIso (AdicReduction.Construction.adicReductionMap (I ^ n) φ) :=
    AdicReduction.Construction.adicReductionMap_quasiIso (I ^ n) φ
  exact reducedKernelComparison_surjective_of_finite_model I φ

theorem cochainFormalZeroCycleComparison_surjective_of_tensor_finite_model [IsNoetherianRing R]
    [Module.Finite R (C.X 0)] [Module.Finite R (C.X 1)]
    (hφ : ∀ n, QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I ^ n) φ)) :
    Function.Surjective (cochainFormalZeroCycleComparison I D) :=
  reducedKernelComparison_surjective_of_tensor_finite_model I φ hφ

theorem formalZeroCycleComparisonSurjective_of_tensor_finite_model [IsNoetherianRing R]
    [Module.Finite R (C.X 0)] [Module.Finite R (C.X 1)]
    (hφ : ∀ n, QuasiIso (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (R ⧸ I ^ n) φ)) :
    FormalZeroCycleComparisonSurjective I D :=
  cochainFormalZeroCycleComparison_surjective_of_tensor_finite_model I φ hφ

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.FiniteModelCompletion.Construction
