import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Gelfand -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Gelfand

noncomputable section

/-! A finite-support proof of the Gelfand involution criterion. It uses
the actual equivariant coset operators and a nondegenerate twisted pairing. -/

open scoped Classical

section Pairing

variable {X : Type*} (θ : X → X)

def twistedPairing : (X →₀ ℚ) →ₗ[ℚ] Module.Dual ℚ (X →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun x => Finsupp.lapply (θ x))

theorem twistedPairing_single (x : X) (r : ℚ) (f : X →₀ ℚ) :
    twistedPairing θ (Finsupp.single x r) f = r * f (θ x) := by
  rw [twistedPairing, Finsupp.linearCombination_single]
  rfl

theorem twistedPairing_apply_single (hθ : Function.Involutive θ)
    (f : X →₀ ℚ) (x : X) (r : ℚ) :
    twistedPairing θ f (Finsupp.single x r) = r * f (θ x) := by
  have heq : (twistedPairing θ).flip (Finsupp.single x r) = r • Finsupp.lapply (θ x) := by
    apply Finsupp.lhom_ext
    intro y a
    change twistedPairing θ (Finsupp.single y a) (Finsupp.single x r) =
      r * (Finsupp.single y a) (θ x)
    rw [twistedPairing_single]
    by_cases h : x = θ y
    · have h' : θ x = y := by rw [h, hθ y]
      simp only [Finsupp.single_apply, ite_eq_left h, ite_eq_left h'.symm]
      exact mul_comm _ _
    · have h' : y ≠ θ x := by
        intro hy
        apply h
        rw [hy, hθ x]
      simp only [Finsupp.single_apply, ite_eq_right h, ite_eq_right h', mul_zero]
  exact congrArg (fun l : Module.Dual ℚ (X →₀ ℚ) => l f) heq

end Pairing

variable {G : Type*} [Group G] (U : Subgroup G) (θ : G ≃* G)
  (hU : ∀ g : G, θ g ∈ U ↔ g ∈ U)

def quotientTwist : G ⧸ U → G ⧸ U :=
  Quotient.map θ (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (hU _).mpr (QuotientGroup.leftRel_apply.mp hab))

@[simp]
theorem quotientTwist_mk (g : G) :
    quotientTwist U θ hU (QuotientGroup.mk g) = QuotientGroup.mk (θ g) := rfl

theorem quotientTwist_involutive (hθ : Function.Involutive θ) :
    Function.Involutive (quotientTwist U θ hU) := by
  intro x
  induction x using Quotient.inductionOn with
  | h x => simp only [quotientTwist_mk, hθ x]

theorem hecke_apply_single (T : HeckeKernel.SphericalHecke U) (g : G) (r : ℚ) (x : G ⧸ U) :
    T.val (Finsupp.single (QuotientGroup.mk g) r) x =
      r * HeckeKernel.kernel U T (g⁻¹ • x) := by
  have hs : Finsupp.single (QuotientGroup.mk g : G ⧸ U) r =
      r • Finsupp.single (QuotientGroup.mk g) 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, HeckeKernel.hecke_single, CentralConvolution.translate_apply]

include hU in
/-- If the anti-involution g ↦ θ(g)^-1 fixes every bi-level kernel,
every Hecke operator is self-adjoint for one nondegenerate pairing. -/
theorem hecke_twisted_selfAdjoint (hθ : Function.Involutive θ)
    (hanti : ∀ (T : HeckeKernel.SphericalHecke U) (g : G),
      HeckeKernel.kernel U T (QuotientGroup.mk (θ g)⁻¹) = HeckeKernel.kernel U T (QuotientGroup.mk g))
    (T : HeckeKernel.SphericalHecke U) (f g : HeckeKernel.CosetModule U) :
    twistedPairing (quotientTwist U θ hU) (T.val f) g =
      twistedPairing (quotientTwist U θ hU) f (T.val g) := by
  have heq : (twistedPairing (quotientTwist U θ hU)).comp T.val =
      T.val.dualMap.comp (twistedPairing (quotientTwist U θ hU)) := by
    apply Finsupp.lhom_ext
    intro x r
    apply Finsupp.lhom_ext
    intro y t
    change twistedPairing (quotientTwist U θ hU) (T.val (Finsupp.single x r))
      (Finsupp.single y t) =
        twistedPairing (quotientTwist U θ hU) (Finsupp.single x r)
          (T.val (Finsupp.single y t))
    rw [twistedPairing_apply_single _ (quotientTwist_involutive U θ hU hθ),
      twistedPairing_single]
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        rw [quotientTwist_mk, quotientTwist_mk, hecke_apply_single, hecke_apply_single]
        have hh := hanti T (x⁻¹ * θ y)
        simp only [map_mul, map_inv, hθ y, mul_inv_rev, inv_inv] at hh
        change t * (r * HeckeKernel.kernel U T (QuotientGroup.mk (x⁻¹ * θ y))) =
          r * (t * HeckeKernel.kernel U T (QuotientGroup.mk (y⁻¹ * θ x)))
        rw [hh]
        ring
  exact LinearMap.congr_fun (LinearMap.congr_fun heq f) g

include hU in
/-- The Gelfand criterion proves commutativity inside the existing
spherical algebra; no commutative multiplication is supplied. -/
theorem spherical_commutative_of_involution (hθ : Function.Involutive θ)
    (hanti : ∀ (T : HeckeKernel.SphericalHecke U) (g : G),
      HeckeKernel.kernel U T (QuotientGroup.mk (θ g)⁻¹) = HeckeKernel.kernel U T (QuotientGroup.mk g))
    (S T : HeckeKernel.SphericalHecke U) : S * T = T * S := by
  let β := twistedPairing (quotientTwist U θ hU)
  have hself := hecke_twisted_selfAdjoint U θ hU hθ hanti
  have h (f g : HeckeKernel.CosetModule U) : β f ((S * T).val g) = β f ((T * S).val g) := by
    rw [← hself (S * T)]
    change β (S.val (T.val f)) g = β f (T.val (S.val g))
    rw [hself S, hself T]
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  ext x
  have hx := h (Finsupp.single (quotientTwist U θ hU x) 1) g
  simpa only [β, twistedPairing_single, quotientTwist_involutive U θ hU hθ x, one_mul] using hx

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Gelfand
