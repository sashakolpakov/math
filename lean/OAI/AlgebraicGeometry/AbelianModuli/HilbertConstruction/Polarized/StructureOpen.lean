import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.StructureOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.CohomologyDimensions

/-! # Structure Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every actual tame polarized full-level fiber belongs to the
structure-sheaf H1 bound open. The criterion is invariant under the
original isomorphisms of abelian schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

section

theorem Abelian.Schemes.AbelianScheme.structureH1Dimension_eq_ground
    {K : Type u} [Field K] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    A.structureH1Dimension =
      Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) 1).obj (Line.Bundles.structureModule A.scheme.left)) := by
  let e : Γ(Spec (.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hmap : (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom).comp e.toRingHom = A.scheme.hom.appTop.hom := by
    ext r
    change A.scheme.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv
      ((Scheme.ΓSpecIso (.of K)).hom r)) = A.scheme.hom.appTop r
    exact congrArg A.scheme.hom.appTop
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of K)).hom_inv_id r)
  let H := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) 1).obj (Line.Bundles.structureModule A.scheme.left)
  let a := CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso e.toRingHom (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom)
    (Line.Bundles.structureModule A.scheme.left) 1 ≪≫
      CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hmap (Line.Bundles.structureModule A.scheme.left) 1
  exact a.toLinearEquiv.finrank_eq.symm.trans (Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e H)

theorem Abelian.Schemes.AbelianScheme.structureH1Dimension_eq_of_iso
    {K : Type u} [Field K] {g : ℕ}
    (A B : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (e : A.scheme ≅ B.scheme) :
    A.structureH1Dimension = B.structureH1Dimension := by
  let f := e.hom.left
  let : IsIso f := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map e.hom))
  let : B.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.scheme.hom]
    infer_instance⟩
  let eP := CohomologyPullbackIso.lineBundleCohomologyPullbackIso f B.scheme.hom (Line.Bundles.LineBundle.trivial B.scheme.left) 1
  let eS := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ B.scheme.hom)) 1).mapIso (Line.Bundles.structureModulePullbackIso f)
  have h := eS.toLinearEquiv.finrank_eq.symm.trans eP.toLinearEquiv.finrank_eq
  have hbase : f ≫ B.scheme.hom = A.scheme.hom := e.hom.w
  rw [hbase] at h
  exact A.structureH1Dimension_eq_ground.trans
    (h.trans B.structureH1Dimension_eq_ground.symm)

end

theorem PolarizationData.PolarizedAbelianWithFullLevel.structureH1Dimension_eq
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hNK : (N : K) ≠ 0) : A.abelian.structureH1Dimension = g := by
  rw [A.abelian.structureH1Dimension_eq_ground]
  simpa only [Nat.choose_one_right] using A.structure_cohomology_finrank A.dual hN hNK 1

theorem Abelian.Schemes.AbelianScheme.structureH1Open_contains_polarized_fiber
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    {K : Type u} [Field K] (b : Spec (.of K) ⟶ S)
    {N : ℕ} {δ : Fin g → ℕ}
    (B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (e : (A.pullback b).scheme ≅ B.abelian.scheme)
    (hN : 3 ≤ N) (hNK : (N : K) ≠ 0) :
    Set.range b ⊆ (A.structureH1Open P g : Set S) := by
  apply (A.structureH1Open_field_point P g b).mpr
  exact ((A.pullback b).structureH1Dimension_eq_of_iso B.abelian e).le.trans
    (B.structureH1Dimension_eq hN hNK).le

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
