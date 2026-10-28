import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalReducedPolarizedRigidity

/-! # Characteristic Zero Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPolarizedRigidity

noncomputable section

/-! Over a countable characteristic-zero field, the arithmetic rigidity
coefficient is already a unit. The actual full-level automorphisms on all
reduced tests are therefore trivial without further localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem characteristicZero_polarized_reduced_rigidity
    {K : Type} [Field K] [CharZero K] [Countable K]
    {S : Scheme.{0}} [IsNoetherian S] (p : S ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (T : Over S) [IsReduced T.left]
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)) :
    e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme := by
  obtain ⟨r, hr, hrigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away (RingHom.id K)
    Function.injective_id p A hN hPresentations
  apply hrigid T e
  intro x hx
  exact (p (T.hom x)).isPrime.ne_top
    ((p (T.hom x)).asIdeal.eq_top_of_isUnit_mem hx (isUnit_iff_ne_zero.mpr hr))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPolarizedRigidity
