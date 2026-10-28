import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniversalPolarizedRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismStratum

/-! # Stratum Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.StratumRigidity

noncomputable section

/-! Uniform arithmetic rigidity on one bounded graph-polynomial stratum.
The universal equality is pulled back to every reduced test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem polarized_stratum_rigidity_away
    {R K : Type} [CommRing R] [IsDomain R] [Field K] [CharZero K] [Countable K]
    (ι : R →+* K) (hι : Function.Injective ι)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (p : S ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (Q : Polynomial ℚ) :
    ∃ r : R, r ≠ 0 ∧ ∀ (T : Over S) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
      (∀ t : T.left, AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial
        (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) (T.hom t) = Q) →
      (∀ x : T.left, r ∉ (p (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (A.abelian.pullback T.hom).scheme := by
  obtain ⟨Z, hr, hn, hft, _, _, u, hc⟩ :=
    AutomorphismStratum.exists_bounded_polarized_automorphism_stratum A P d hP s hs he hPresentations Q
  have : IsReduced Z.left := hr
  have : IsNoetherian Z.left := hn
  have : LocallyOfFiniteType Z.hom := hft
  obtain ⟨r, hnonzero, hid⟩ := UniversalPolarizedRigidity.universal_polarized_automorphism_identity_away
    ι hι (Z.hom ≫ p) (A.pullback Z.hom) u hN
  refine ⟨r, hnonzero, ?_⟩
  intro T _ e hT hunit
  obtain ⟨f, hf⟩ := hc T e hT
  have hfi (x : T.left) : r ∉ ((Z.hom ≫ p) (f.left x)).asIdeal := by
    have hx : (Z.hom ≫ p) (f.left x) = p (T.hom x) :=
      congrArg p (congrArg (fun q : T.left ⟶ S => q x) f.w)
    exact hx.symm ▸ hunit x
  have hu := hid f.left hfi
  have hres : EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f (Finite.Actions.GroupEndRing.ofHom _ u.abelian.hom) =
      EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f 1 := (Relative.EndomorphismEquationLocus.restrict_groupEnd_eq_iff A.abelian f _ 1).mpr hu
  have hv : Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom = (1 : Finite.Actions.GroupEndRing (A.abelian.pullback T.hom)) :=
    hf.symm.trans (hres.trans (map_one (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f)))
  exact congrArg (Finite.Actions.GroupEndRing.hom (A.abelian.pullback T.hom)) hv

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.StratumRigidity
