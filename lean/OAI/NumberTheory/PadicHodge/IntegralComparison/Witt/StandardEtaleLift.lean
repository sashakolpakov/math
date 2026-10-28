import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import Mathlib.RingTheory.Polynomial.Basic

/-! # Standard Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift

noncomputable section

/-! Smooth flat Witt lifts of the actual standard etale coordinate algebras. -/

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) (σ : Type v) (C : Type u) [Field k] [Fintype k] [CharP k p]
  [Finite σ] [CommRing C] [Algebra k C] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] (P : StandardEtalePresentation (MvPolynomial σ k) C)

local notation "W" => WittVector p k
local notation "R" => MvPolynomial σ W
local notation "S" => MvPolynomial σ k

instance residueAlgebra : Algebra R S :=
  (MvPolynomial.map (WittVector.constantCoeff : W →+* k)).toAlgebra

omit [Fintype k] [CharP k p] [Finite σ] in
theorem residue_surjective : Function.Surjective (algebraMap R S) :=
  MvPolynomial.map_surjective WittVector.constantCoeff (WittVector.constantCoeff_surjective p)

abbrev Ring := StandardEtaleLiftAlgebra.Ring S (residue_surjective p k σ) P.P

instance wittAlgebra : Algebra W (Ring p k σ C P) :=
  ((algebraMap R (Ring p k σ C P)).comp MvPolynomial.C).toAlgebra

instance wittTower : IsScalarTower W R (Ring p k σ C P) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance smooth : Algebra.Smooth W (Ring p k σ C P) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra.Smooth W R := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp W R (Ring p k σ C P)

instance flat : Module.Flat W (Ring p k σ C P) := Algebra.Smooth.flat W (Ring p k σ C P)

def reduction : Ring p k σ C P →+* C :=
  P.equivRing.symm.toRingHom.comp
    (StandardEtaleLiftAlgebra.reduction S (residue_surjective p k σ) P.P)

omit [Algebra k C] [IsScalarTower k S C] [Fintype k] [CharP k p] [Finite σ] in
theorem reduction_surjective : Function.Surjective (reduction p k σ C P) :=
  P.equivRing.symm.surjective.comp
    (StandardEtaleLiftAlgebra.reduction_surjective S (residue_surjective p k σ) P.P)

omit [Fintype k] [CharP k p] [Finite σ] in
theorem reduction_base (w : W) : reduction p k σ C P (algebraMap W (Ring p k σ C P) w) =
    algebraMap k C (WittVector.constantCoeff w) := by
  change P.equivRing.symm (StandardEtaleLiftAlgebra.reduction S (residue_surjective p k σ) P.P
    (algebraMap R (Ring p k σ C P) (MvPolynomial.C w))) = _
  rw [StandardEtaleLiftAlgebra.reduction_base, P.equivRing.symm.commutes]
  change algebraMap S C (MvPolynomial.map WittVector.constantCoeff (MvPolynomial.C w)) = _
  rw [MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply k S C (WittVector.constantCoeff w)).symm

omit [Algebra k C] [IsScalarTower k S C] [Finite σ] in
theorem reduction_kernel : RingHom.ker (reduction p k σ C P) =
    Ideal.span {(p : Ring p k σ C P)} := by
  have h : RingHom.ker (reduction p k σ C P) =
      RingHom.ker (StandardEtaleLiftAlgebra.reduction S (residue_surjective p k σ) P.P) :=
    RingHom.ker_comp_of_injective _ (show Function.Injective P.equivRing.symm.toRingHom from
      P.equivRing.symm.injective)
  rw [h, StandardEtaleLiftAlgebra.reduction_kernel]
  change (RingHom.ker (MvPolynomial.map (WittVector.constantCoeff : W →+* k))).map
    (algebraMap R (Ring p k σ C P)) = _
  rw [MvPolynomial.ker_map, WittVector.ker_constantCoeff,
    Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.map_span, Set.image_singleton, map_natCast]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift
