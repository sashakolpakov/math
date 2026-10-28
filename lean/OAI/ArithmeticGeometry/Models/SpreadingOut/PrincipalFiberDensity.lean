import OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFlatShrink
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents

/-! # Principal Fiber Density -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFiberDensity.Construction

noncomputable section

/-! A principal open remains dense in all field fibers after a suitable
shrinking of a Dedekind base. Empty affine fibers are allowed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem specMap_dominant_of_injective
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

theorem tensor_localization_injective_of_flat_quotient
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (b : B)
    (hb : Function.Injective (fun x : B ↦ b * x))
    [Module.Flat R (B ⧸ Ideal.span ({b} : Set B))] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R S)
      (IsScalarTower.toAlgHom R B (Localization.Away b))) := by
  let e := IsLocalization.Away.tensorProductEquivTMulRight R S b (Localization.Away b)
  have he (x : S ⊗[R] B) : e (Algebra.TensorProduct.map (AlgHom.id R S)
      (IsScalarTower.toAlgHom R B (Localization.Away b)) x) =
      algebraMap (S ⊗[R] B) (Localization.Away (1 ⊗ₜ[R] b : S ⊗[R] B)) x := by
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      change e (s ⊗ₜ[R] algebraMap B (Localization.Away b) x) = _
      exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := S) B b (Localization.Away b) s x
    | add x y hx hy => simp only [map_add, hx, hy]

  have hinj := FiberDomainTransfer.Construction.away_algebraMap_injective_of_mul_injective (S ⊗[R] B)
    (1 ⊗ₜ[R] b) (FiberRegularity.Construction.tensor_mul_injective_of_flat_quotient R B S b hb)
  intro x y h
  apply hinj
  have H := congrArg e h
  rwa [he, he] at H

theorem principal_fiber_map_dominant_of_flat_quotient
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (b : B)
    (hb : Function.Injective (fun x : B ↦ b * x))
    [Module.Flat R (B ⧸ Ideal.span ({b} : Set B))] :
    IsDominant (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R S)
        (IsScalarTower.toAlgHom R B (Localization.Away b))).toRingHom)) :=
  specMap_dominant_of_injective _ (tensor_localization_injective_of_flat_quotient R S B b hb)

theorem principal_open_dense_in_all_fibers_after_shrinking
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B]
    (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra (Localization.Away r) S],
        IsDominant (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id (Localization.Away r) S)
            (IsScalarTower.toAlgHom (Localization.Away r) (Localization.Away r ⊗[R] B)
              (Localization.Away (1 ⊗ₜ[R] b : Localization.Away r ⊗[R] B)))).toRingHom)) := by
  obtain ⟨r, hr, hf⟩ := PrincipalFlatShrink.Construction.principal_quotient_flat_after_inverting_base_element R B b
  have := hf
  refine ⟨r, hr, fun S _ _ ↦ ?_⟩
  apply principal_fiber_map_dominant_of_flat_quotient
  change Function.Injective (LinearMap.mulLeft R (1 ⊗ₜ[R] b : Localization.Away r ⊗[R] B))
  rw [PrincipalFlatShrink.Construction.tensor_mulLeft_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.mulLeft R b)
    (mul_right_injective₀ hb)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFiberDensity.Construction
