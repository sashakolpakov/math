import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Flat.Localization

/-! # Smooth Integral Closure -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralClosure.Construction

noncomputable section

/-!
# Completion: integral closedness after smooth base change

If the base is integrally closed in an algebra, its smooth base change is
integrally closed in the corresponding tensor product. This will control
the components of smooth and étale charts through their generic fibers.
-/

open scoped TensorProduct

universe u v w

variable (R : Type u) (S : Type v) (B : Type w)
  [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  [Algebra.Smooth R S] [IsIntegrallyClosedIn R B]

omit [Algebra.Smooth R S] in
/-- Tensoring the original integral closure introduces only elements of the new base. -/
theorem smooth_integralClosure_tensor_image (z : S ⊗[R] integralClosure R B) :
    ∃ s : S, Algebra.TensorProduct.map (AlgHom.id R S) (integralClosure R B).val z =
      algebraMap S (S ⊗[R] B) s := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht =>
    obtain ⟨s, hs⟩ := hz
    obtain ⟨r, hr⟩ := ht
    exact ⟨s + r, by simp only [map_add, hs, hr]⟩
  | tmul s b =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral b.property
    refine ⟨s * algebraMap R S r, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    rw [← hr]
    change s ⊗ₜ[R] (algebraMap R B) r = (s * algebraMap R S r) ⊗ₜ[R] (1 : B)
    rw [show (algebraMap R B) r = r • (1 : B) by simp [Algebra.smul_def]]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [Algebra.smul_def, mul_comm]

/-- Integral closedness in an algebra is preserved by smooth base change. -/
theorem smooth_integrallyClosedIn_baseChange : IsIntegrallyClosedIn S (S ⊗[R] B) := by
  refine ⟨Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := S) (B := B)
    (IsIntegralClosure.algebraMap_injective R R B), ?_, ?_⟩
  · intro x
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := B)).surjective ⟨_, x⟩
    obtain ⟨s, hs⟩ := smooth_integralClosure_tensor_image R S B z
    refine ⟨s, hs.symm.trans ?_⟩
    exact congrArg Subtype.val hz
  · rintro ⟨s, rfl⟩
    exact isIntegral_algebraMap

omit [Algebra.Smooth R S] in
/-- The same integral-closedness comparison holds for arbitrary localizations. -/
theorem localization_integrallyClosedIn_baseChange (M : Submonoid R) [IsLocalization M S] :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  have : Module.Flat R S := IsLocalization.flat S M
  refine ⟨Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := S) (B := B)
    (IsIntegralClosure.algebraMap_injective R R B), ?_, ?_⟩
  · intro hx
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_isLocalization
      (R := R) (S := S) (B := B) M).surjective ⟨_, hx⟩
    obtain ⟨s, hs⟩ := smooth_integralClosure_tensor_image R S B z
    exact ⟨s, hs.symm.trans (congrArg Subtype.val hz)⟩
  · rintro ⟨s, rfl⟩
    exact isIntegral_algebraMap

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralClosure.Construction
