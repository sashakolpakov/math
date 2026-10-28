import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.StratumRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.OpenPolarizedRigidity

/-! # Reduced Polarized Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ReducedPolarizedRigidity

noncomputable section

/-! Bounded source-polynomial strata give one arithmetic localization
on which polarized full-level automorphisms are trivial on every
reduced test scheme, including tests which are not noetherian. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem affine_polarized_reduced_rigidity_away
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (p : S ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) :
    ∃ r : R, r ≠ 0 ∧ ∀ (T : Over S) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
      (∀ x : T.left, r ∉ (p (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme := by
  classical
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  obtain ⟨d, _, P, hP, n, s, hs, he⟩ := PolarizationEmbedding.polarized_exists_affine_section_embedding A
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let Φ := Polarized.AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial BA
  have hΦ : IsLocallyConstant Φ := Polarized.AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial_isLocallyConstant BA
  let I := Set.range Φ
  let : Finite I := hΦ.range_finite.to_subtype
  let : Fintype I := Fintype.ofFinite I
  choose r hnonzero hrigid using fun i : I => Polarized.StratumRigidity.polarized_stratum_rigidity_away
    ι hι p A hN hPresentations P d hP s hs he i.val
  let U : I → S.Opens := fun i => ⟨{x | Φ x = i.val}, hΦ.isOpen_fiber i.val⟩
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨⟨Φ x, ⟨x, rfl⟩⟩, rfl⟩
  exact IntegralModel.Finite.OpenPolarizedRigidity.finite_open_polarized_rigidity_away p A U hU r hnonzero
    (fun i T _ e hT hunit => hrigid i T e hT hunit)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ReducedPolarizedRigidity
