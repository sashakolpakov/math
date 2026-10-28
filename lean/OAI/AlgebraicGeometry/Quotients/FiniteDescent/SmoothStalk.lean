import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothClosed
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Stalk -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial

noncomputable section

/-! Factoriality of the actual stalks of a smooth scheme over an algebraically closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem stalk {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let ρ : K →+* Γ(X, U) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U le_top).hom
  have hρ : ρ.Smooth :=
    (RingHom.Smooth.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)).mpr
        (f.smooth_appLE (isAffineOpen_top (Spec (.of K))) hU le_top)
  let : Algebra K Γ(X, U) := ρ.toAlgebra
  have : Algebra.Smooth K Γ(X, U) := hρ
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : UniqueFactorizationMonoid (Localization.AtPrime p) :=
    SmoothClosed.Construction.SmoothClosedFactorial.at_prime (K := K) p
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (X.presheaf.stalk x)
  exact e.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial
