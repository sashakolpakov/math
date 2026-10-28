import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericPolarizedAutomorphismSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationOpenSupport

/-! # Universal Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniversalPolarizedRigidity

noncomputable section

/-! A fixed universal polarized full-level automorphism becomes the
identity after one coefficient is inverted, on every test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem universal_polarized_automorphism_identity_away
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {Z : Scheme.{0}} [IsNoetherian Z] [IsReduced Z]
    (p : Z ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Z)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N) :
    ∃ r : R, r ≠ 0 ∧ ∀ {T : Scheme.{0}} (t : T ⟶ Z),
      (∀ x : T, r ∉ (p (t x)).asIdeal) →
      (Over.pullback t).map e.abelian.hom = (Over.pullback t).map (𝟙 A.abelian.scheme) := by
  obtain ⟨r, hr, hs⟩ := GenericPolarizedAutomorphismSupport.polarized_automorphism_identity_away ι hι p A e hN
  let U : Z.Opens := p ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨r, hr, fun t ht => ?_⟩
  exact SmoothEquationOpenSupport.equation_of_open_support e.abelian.hom (𝟙 A.abelian.scheme) U
    (fun z hz => hs z hz) t ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniversalPolarizedRigidity
