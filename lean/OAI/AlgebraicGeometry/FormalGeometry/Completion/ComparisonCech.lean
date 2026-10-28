import OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseCechCycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.FiniteModelCompletion

/-! # Comparison Cech -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonCech.Construction

noncomputable section

/-! Transfer the actual Cech formal zero-cycle comparison to the actual formal-functions map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

/-- The actual formal-functions map has exactly the canonical completed Cech coordinates. -/
theorem formalFunctionsComparison_cech (x : AdicCompletion I R) :
    Infinitesimal.CompatibleCycles.Construction.infinitesimalGlobalSectionsCompatibleCyclesEquiv I f U hU hcover
      (FunctionsComparison.Construction.formalFunctionsComparison I f x) =
        CompatibleReducedKernels.Construction.reducedKernelComparison I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom
          (AdicCompletion.map I (BaseCechCycles.Construction.baseCechCycleMap f U hcover) x) := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I R x
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact Infinitesimal.CompatibleCycles.Construction.adicZerothQuotient_eq I _ _
  | succ n =>
    rw [Infinitesimal.CompatibleCycles.Construction.infinitesimalGlobalSectionsCompatibleCyclesEquiv_coordinate]
    change (Infinitesimal.CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n
      (FunctionsComparison.Construction.infinitesimalBaseSectionsMap I f n
        (AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I R s)))).val = _
    rw [AdicCompletion.evalₐ_mk]
    exact BaseCechCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_base_mk f U hcover I hU n (s (n + 1))

include hU hcover in
/-- Once the actual global-section map is an isomorphism, actual Cech formal zero-cycle
surjectivity gives surjectivity of the original formal-functions ring homomorphism. -/
theorem formalFunctionsComparison_surjective_of_cech [IsIso f.appTop]
    (h : Completion.Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)) :
    Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I f) := by
  intro s
  obtain ⟨z, hz⟩ := h (Infinitesimal.CompatibleCycles.Construction.infinitesimalGlobalSectionsCompatibleCyclesEquiv I f U hU hcover s)
  let e := LinearEquiv.ofBijective (BaseCechCycles.Construction.baseCechCycleMap f U hcover)
    (BaseCechCycles.Construction.baseCechCycleMap_bijective f U hcover)
  obtain ⟨x, hx⟩ := (AdicCompletion.congr I e).surjective z
  refine ⟨x, (Infinitesimal.CompatibleCycles.Construction.infinitesimalGlobalSectionsCompatibleCyclesEquiv I f U hU hcover).injective ?_⟩
  rw [formalFunctionsComparison_cech]
  change AdicCompletion.map I (BaseCechCycles.Construction.baseCechCycleMap f U hcover) x = z at hx
  rw [hx]
  exact hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonCech.Construction
