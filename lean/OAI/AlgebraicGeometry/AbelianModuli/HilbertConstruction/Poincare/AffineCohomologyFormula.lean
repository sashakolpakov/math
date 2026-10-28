import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineNeighborhoodCohomology

/-! # Affine Cohomology Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On every affine open of the dual variety, the actual Poincare family has cohomology concentrated in degree g. Its top cohomology is the quotient by the actual inverse image of the zero section, including the empty inverse-image case. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareAffine_cohomology_formula
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t] :
    let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom;
    let b := pullback.snd p t;
    let L := D.poincare.pullback (pullback.fst p t);
    (∀ q : ℕ, q ≠ g → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom g).obj L.sheaf) ≅
      ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⧸ D.poincareAffineParameterIdeal t)) := by
  classical
  by_cases hx : η[D.abelian.scheme].left (IsLocalRing.closedPoint K) ∈ Set.range t
  · exact A.poincareAffine_neighborhood_cohomology_residue D hg hN hNk t hx
  · have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ D.abelian.scheme.hom)
    have : IsNoetherianRing Γ(T, ⊤) :=
      isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion T.isoSpec.inv)
    have hoff : t ⁻¹' Set.range η[D.abelian.scheme].left = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x h
      obtain ⟨y, hy⟩ := h
      apply hx
      exact ⟨x, hy.symm.trans (congrArg η[D.abelian.scheme].left
        (@Subsingleton.elim (PrimeSpectrum K) inferInstance y (IsLocalRing.closedPoint K)))⟩
    have hI : D.poincareAffineParameterIdeal t = ⊤ := by
      erw [Dual.Data.DualAbelianData.poincareAffineParameterIdeal, Affine.ParameterVanishingIdeal.affineParameterVanishingIdeal,
        hoff, Set.image_empty, PrimeSpectrum.vanishingIdeal_empty]
    have hQ : IsZero (ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⧸ D.poincareAffineParameterIdeal t)) := by
      rw [hI]
      exact ModuleCat.isZero_of_subsingleton _
    have hvan := D.poincareAffine_coefficientCohomology_vanish_off_zero t hoff
    exact ⟨fun q _ => hvan q, ⟨(hvan g).iso hQ⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
