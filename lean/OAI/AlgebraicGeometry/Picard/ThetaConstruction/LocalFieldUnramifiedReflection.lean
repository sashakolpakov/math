import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalUnramifiedFiberReflection
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Local Field Unramified Reflection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalFieldUnramifiedReflection.Geometric

noncomputable section

/-! A local field-valued point detects vanishing of finite modules
over its local source. Thus an actual unramified geometric fiber
reflects formal unramifiedness at the original local point, without
requiring flatness of the original morphism. -/

open scoped TensorProduct

universe u

theorem finiteLocalModule_subsingleton_of_localField
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K]
    [Algebra B K] [IsLocalHom (algebraMap B K)]
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    [Subsingleton (K ⊗[B] M)] : Subsingleton M := by
  let k := IsLocalRing.ResidueField B
  let : Algebra k K := (IsLocalRing.ResidueField.lift (algebraMap B K)).toAlgebra
  let : IsScalarTower B k K := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (IsLocalRing.ResidueField.lift_residue_apply (algebraMap B K) r).symm)
  let : Subsingleton (K ⊗[k] (k ⊗[B] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B k K K M).injective.subsingleton
  have hk : Subsingleton (k ⊗[B] M) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k K).mp inferInstance
  exact (IsLocalRing.subsingleton_tensorProduct (R := B) (M := M)).mp hk

theorem localAlgebra_formallyUnramified_of_localFieldFiber
    (R B K : Type u) [CommRing R] [CommRing B] [IsLocalRing B] [Field K]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]
    [IsLocalHom (algebraMap B K)] [Algebra.EssFiniteType R B]
    [Algebra.FormallyUnramified K (K ⊗[R] B)] : Algebra.FormallyUnramified R B := by
  let : Algebra B (K ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Subsingleton (K ⊗[R] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R K B (K ⊗[R] B)).injective.subsingleton
  let : Subsingleton (K ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mapOfCompatibleSMul_surjective B R R K Ω[B⁄R]).subsingleton
  exact ⟨finiteLocalModule_subsingleton_of_localField B K Ω[B⁄R]⟩

theorem localAlgebra_formallyUnramified_of_rightLocalFieldFiber
    (R B K : Type u) [CommRing R] [CommRing B] [IsLocalRing B] [Field K]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K]
    [IsLocalHom (algebraMap B K)] [Algebra.EssFiniteType R B]
    (h : let : Algebra K (B ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
      Algebra.FormallyUnramified K (B ⊗[R] K)) : Algebra.FormallyUnramified R B := by
  let : Algebra K (B ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  let := h
  let : Subsingleton (K ⊗[R] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R K B (B ⊗[R] K)).injective.subsingleton
  let : Subsingleton (K ⊗[B] Ω[B⁄R]) :=
    (TensorProduct.mapOfCompatibleSMul_surjective B R R K Ω[B⁄R]).subsingleton
  exact ⟨finiteLocalModule_subsingleton_of_localField B K Ω[B⁄R]⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.LocalFieldUnramifiedReflection.Geometric
