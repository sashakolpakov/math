import OAI.ArithmeticGeometry.Models.SpreadingOut.RootScalarExtension
import Mathlib.RingTheory.Localization.BaseChange

/-! # Hypersurface Chart Base Change -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChartBaseChange.Construction

noncomputable section

/-! Scalar extension of a principal monic hypersurface chart. -/

open scoped TensorProduct

universe u

def hypersurfaceChartScalarExtensionIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R)) (d : MvPolynomial (Fin n) R) :
    S ⊗[R] Localization.Away (algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p) d) ≃ₐ[S]
      Localization.Away (algebraMap (MvPolynomial (Fin n) S)
        (AdjoinRoot (Polynomial.map (MvPolynomial.map (algebraMap R S)) p))
          (MvPolynomial.map (algebraMap R S) d)) := by
  let c := algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p) d
  let e₁ := IsLocalization.Away.tensorProductEquivTMulRight R S c (Localization.Away c)
  let e := RootScalarExtension.Construction.rootScalarExtensionIso R S n p
  refine e₁.trans (IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (1 ⊗ₜ[R] c : S ⊗[R] AdjoinRoot p))
    (T := Submonoid.powers (algebraMap (MvPolynomial (Fin n) S)
      (AdjoinRoot (Polynomial.map (MvPolynomial.map (algebraMap R S)) p))
      (MvPolynomial.map (algebraMap R S) d))) _ _ e ?_)
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (RootScalarExtension.Construction.rootScalarExtensionIso_one_tmul_algebraMap R S n p d)

theorem hypersurface_chart_generic_iso_of_coefficients
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (n : ℕ) (p₀ : Polynomial (MvPolynomial (Fin n) R)) (d₀ : MvPolynomial (Fin n) R)
    (p : Polynomial (MvPolynomial (Fin n) K)) (d : MvPolynomial (Fin n) K)
    (hp : Polynomial.map (MvPolynomial.map (algebraMap R K)) p₀ = p)
    (hd : MvPolynomial.map (algebraMap R K) d₀ = d) :
    Nonempty (K ⊗[R] Localization.Away (algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p₀) d₀) ≃ₐ[K]
      Localization.Away (algebraMap (MvPolynomial (Fin n) K) (AdjoinRoot p) d)) := by
  subst p
  subst d
  exact ⟨hypersurfaceChartScalarExtensionIso R K n p₀ d₀⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChartBaseChange.Construction
