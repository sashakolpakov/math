import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicKernelScalarRestriction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainScalarRestriction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.FiniteModelCompletion

/-! # Cycles Transport -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CyclesTransport.Construction

noncomputable section

/-! Transport actual formal zero-cycle surjectivity across scalar restrictions and complex isomorphisms. -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem formalZeroCycleComparisonSurjective_restrictScalars (ρ : R →+* S) (I : Ideal R)
    (C : CochainComplex (ModuleCat.{u} S) ℕ)
    (h : Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective (I.map ρ) C) :
    Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I (CochainScalarRestriction.Construction.scalarRestrictedComplex ρ C) := by
  let : Algebra R S := ρ.toAlgebra
  let : Module R (C.X 0) := Module.compHom (C.X 0) ρ
  let : Module R (C.X 1) := Module.compHom (C.X 1) ρ
  have : IsScalarTower R S (C.X 0) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S (C.X 1) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact AdicKernelScalarRestriction.Construction.reducedKernelComparison_surjective_restrictScalars I (C.d 0 1).hom h

theorem formalZeroCycleComparisonSurjective_of_iso (I : Ideal R)
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (e : C ≅ D)
    (h : Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I C) :
    Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I D := by
  let (n : ℕ) : QuasiIso (AdicReduction.Construction.adicReductionMap (I ^ n) e.hom) :=
    inferInstanceAs (QuasiIso
      (((AdicReduction.Construction.adicReductionFunctor (I ^ n)).mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom))
  intro x
  obtain ⟨y, hy⟩ := (CochainReducedKernels.Construction.compatibleReducedCochainMap_bijective e.hom I).surjective x
  obtain ⟨z, hz⟩ := h y
  change CompatibleReducedKernels.Construction.reducedKernelComparison I (C.d 0 1).hom z = y at hz
  refine ⟨AdicCompletion.map I (CochainReducedKernels.Construction.cochainKernelMap e.hom) z, ?_⟩
  change CompatibleReducedKernels.Construction.reducedKernelComparison I (D.d 0 1).hom
    (AdicCompletion.map I (CochainReducedKernels.Construction.cochainKernelMap e.hom) z) = x
  rw [Finite.FiniteModelCompletion.Construction.reducedKernelComparison_naturality, hz, hy]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CyclesTransport.Construction
