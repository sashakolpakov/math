import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.TruncatedModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ResidueAllCohomologyDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkClosedFieldPoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.CohomologyIsomorphicFieldBase

/-! # Cohomology Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over every field, the actual structure-sheaf cohomology dimensions of the supplied polarized full-level abelian data are choose(g,q) in every degree. The proof constructs the finite model and identifies its residue specialization with the original variety. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.structure_cohomology_finrank
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) q).obj (Line.Bundles.structureModule A.abelian.scheme.left)) =
      g.choose q := by
  let T := D.poincareZeroStalkScheme
  let t := D.poincareZeroStalkParameterMap
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left := pullback.fst p t
  let b : P ⟶ T := pullback.snd p t
  let H : IsPullback a b p t := IsPullback.of_hasPullback p t
  have : IsProper A.abelian.scheme.hom := A.abelian.proper
  have : A.abelian.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.abelian.scheme.hom]; infer_instance⟩
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip inferInstance
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  obtain ⟨k, U, hU, ha, he, C, φ, Q, _, hbound, hfin, hfree, ht, _, _⟩ :=
    A.poincareZeroStalk_exists_dimension_bounded_model D hN hNk
  let R := Γ(T, ⊤)
  let B := IsLocalRing.ResidueField R
  let j : Spec (.of B) ⟶ T := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap R B)
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  let HF : IsPullback (a' ≫ a) b' p (j ≫ t) := H'.paste_horiz H
  let c : Spec (.of B) ⟶ Spec (.of K) := (j ≫ t) ≫ D.abelian.scheme.hom
  let aA := (a' ≫ a) ≫ pullback.snd D.abelian.scheme.hom A.abelian.scheme.hom
  have HA : IsPullback aA b' A.abelian.scheme.hom c :=
    HF.paste_horiz (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip
  have hs : Function.Surjective (algebraMap R B) := by
    change Function.Surjective (algebraMap R (IsLocalRing.ResidueField R))
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  have : IsClosedImmersion j := Affine.QuotientCoefficientMap.affineCoordinateMap_isClosedImmersion (algebraMap R B) hs
  have : IsIso c := Rational.StalkClosedFieldPoint.rationalStalk_closedFieldPoint_structure_isIso
    D.abelian.scheme.hom η[D.abelian.scheme].left η[D.abelian.scheme].w j
  have hdim := D.poincareZeroStalk_residue_structure_cohomology_finrank
    H U hU ha he φ ht hfin hfree hbound Q q
  change Module.finrank B ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap b') q).obj (Line.Bundles.structureModule (CategoryTheory.Limits.pullback b j))) = g.choose q at hdim
  exact (Structure.CohomologyIsomorphicFieldBase.structureCohomology_finrank_isomorphic_field_base HA q).trans hdim

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
