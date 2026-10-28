import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Surjective Module Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleDimension.Constructions

noncomputable section

/-! Restricting scalars along a surjective algebra map preserves
module support dimension. The proof uses the actual annihilator quotient
ring isomorphism, so it applies to each regular-element quotient. -/

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

def annihilatorQuotientIso (hs : Function.Surjective (algebraMap R S)) :
    R ⧸ Module.annihilator R M ≃+* S ⧸ Module.annihilator S M := by
  let f := (Ideal.Quotient.mk (Module.annihilator S M)).comp (algebraMap R S)
  have hk : RingHom.ker f = Module.annihilator R M := by
    dsimp only [f]
    rw [← RingHom.comap_ker, Ideal.mk_ker, Module.comap_annihilator]
  exact (Ideal.quotEquivOfEq hk.symm).trans
    (f.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hs))

theorem supportDim_eq [Module.Finite R M] (hs : Function.Surjective (algebraMap R S)) :
    Module.supportDim R M = Module.supportDim S M := by
  let : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_eq_of_ringEquiv (annihilatorQuotientIso R S M hs)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleDimension.Constructions
