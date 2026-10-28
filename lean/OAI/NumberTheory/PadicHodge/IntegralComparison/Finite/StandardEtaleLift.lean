import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Standard Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.StandardEtaleLift

noncomputable section

/-! A finite standard-etale algebra has a genuine finite etale lift
through a surjective map with nilpotent kernel. The original residue
algebra and its exact Cartesian reduction square are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (h : Function.Surjective (algebraMap R S)) (P : StandardEtalePair S)

abbrev Ring := StandardEtaleLiftAlgebra.Ring S h P
abbrev reduction := StandardEtaleLiftAlgebra.reduction S h P

def residueEquiv : S ⊗[R] StandardEtaleLift.Ring R S h P ≃ₐ[S] P.Ring :=
  (StandardEtaleBaseChange.equivalence (B := S) (StandardEtaleLift.pair (algebraMap R S) h P)).trans
    (IntegralComparison.StandardEtaleLift.residueEquiv (algebraMap R S) h P)

theorem ringPushout : IsPushout (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (algebraMap R (StandardEtaleLift.Ring R S h P)))
    (CommRingCat.ofHom (algebraMap S P.Ring)) (CommRingCat.ofHom (reduction R S h P)) := by
  apply (CommRingCat.isPushout_tensorProduct R S (StandardEtaleLift.Ring R S h P)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (residueEquiv R S h P).toCommRingCatIso
  · simp
  · simp
  · ext s
    exact (residueEquiv R S h P).commutes s
  · ext b
    rfl

theorem square : IsPullback (Spec.map (CommRingCat.ofHom (reduction R S h P)))
    (Spec.map (CommRingCat.ofHom (algebraMap S P.Ring)))
    (Spec.map (CommRingCat.ofHom (algebraMap R (StandardEtaleLift.Ring R S h P))))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (ringPushout R S h P).op.map Scheme.Spec

variable (hnil : IsNilpotent (RingHom.ker (algebraMap R S)))

include hnil in
theorem kernel_nilpotent : IsNilpotent (RingHom.ker (reduction R S h P)) := by
  obtain ⟨N, hN⟩ := hnil
  refine ⟨N, ?_⟩
  rw [StandardEtaleLiftAlgebra.reduction_kernel, ← Ideal.map_pow, hN]
  exact Ideal.map_bot

instance reduction_closed :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (reduction R S h P))) :=
  IsClosedImmersion.spec_of_surjective _ (StandardEtaleLiftAlgebra.reduction_surjective S h P)

include hnil in
theorem reduction_surjective :
    Surjective (Spec.map (CommRingCat.ofHom (reduction R S h P))) := by
  apply NilpotentFiberAmpleness.reduction_surjective _
    (StandardEtaleLiftAlgebra.reduction_surjective S h P)
  obtain ⟨N, hN⟩ := kernel_nilpotent R S h P hnil
  intro b hb
  refine ⟨N, ?_⟩
  have hm : b ^ N ∈ RingHom.ker (reduction R S h P) ^ N := Ideal.pow_mem_pow hb N
  rw [hN] at hm
  exact hm

def reductionHomeomorph : Spec (.of P.Ring) ≃ₜ Spec (.of (StandardEtaleLift.Ring R S h P)) := by
  let i := Spec.map (CommRingCat.ofHom (reduction R S h P))
  let : Surjective i := reduction_surjective R S h P hnil
  exact (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩).homeomorph

variable [IsNoetherianRing R] [Module.Finite S P.Ring]

include hnil in
theorem finite : Module.Finite R (StandardEtaleLift.Ring R S h P) := by
  let : Algebra R P.Ring := ((algebraMap S P.Ring).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S P.Ring := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra (StandardEtaleLift.Ring R S h P) P.Ring := (reduction R S h P).toAlgebra
  let : IsScalarTower R (StandardEtaleLift.Ring R S h P) P.Ring :=
    IsScalarTower.of_algebraMap_eq (fun r => (StandardEtaleLiftAlgebra.reduction_base S h P r).symm)
  let : Algebra.Etale R (StandardEtaleLift.Ring R S h P) := StandardEtaleLiftAlgebra.etale S h P
  let : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) h
  let : Module.Finite R P.Ring := Module.Finite.trans S P.Ring
  let : IsNoetherianRing (StandardEtaleLift.Ring R S h P) := Algebra.FiniteType.isNoetherianRing R (StandardEtaleLift.Ring R S h P)
  let ρ : StandardEtaleLift.Ring R S h P →ₐ[R] P.Ring := IsScalarTower.toAlgHom R (StandardEtaleLift.Ring R S h P) P.Ring
  apply Module.finite_of_surjective_of_ker_le_nilradical ρ
    (StandardEtaleLiftAlgebra.reduction_surjective S h P)
  · have hN := kernel_nilpotent R S h P hnil
    obtain ⟨N, hN⟩ := hN
    intro b hb
    exact ⟨N, hN ▸ Ideal.pow_mem_pow hb N⟩
  · exact IsNoetherian.noetherian _

include hnil in
theorem finite_etale :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (StandardEtaleLift.Ring R S h P)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R (StandardEtaleLift.Ring R S h P)))) := by
  let : Module.Finite R (StandardEtaleLift.Ring R S h P) := finite R S h P hnil
  let : Algebra.Etale R (StandardEtaleLift.Ring R S h P) := StandardEtaleLiftAlgebra.etale S h P
  constructor
  · rw [IsFinite.SpecMap_iff]
    change (algebraMap R (StandardEtaleLift.Ring R S h P)).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap R (StandardEtaleLift.Ring R S h P)).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.StandardEtaleLift
