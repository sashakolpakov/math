import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.CohomologyResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ResidueScalarIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction

/-! # Structural Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical Poincare stalk-family cohomology calculation is linear over the actual local ring of the dual variety, through the canonical global-functions isomorphism of its spectrum. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_structuralCohomology_residue
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    letI : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom;
    let b := pullback.snd p D.poincareZeroStalkParameterMap;
    let L := D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap);
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).obj L.sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) g).obj L.sheaf) ≅
      ModuleCat.of O (IsLocalRing.ResidueField O)) := by
  let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  have : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  let R := Γ(D.poincareZeroStalkScheme, ⊤)
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let b := pullback.snd p D.poincareZeroStalkParameterMap
  let L := D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap)
  let γ : O ≃+* R := (Scheme.ΓSpecIso O).symm.commRingCatIsoToRingEquiv
  have : IsLocalRing R := γ.isLocalRing
  let F := ModuleCat.restrictScalars γ.toRingHom
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareZeroStalk_coefficientCohomology_residue D hg hN hNk
  let E (q : ℕ) : F.obj ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf) ≅
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).obj L.sheaf) :=
    CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso γ.toRingHom b.appTop.hom L.sheaf q
  constructor
  · intro q hq
    exact (F.map_isZero (hvan q hq)).of_iso (E q).symm
  · exact ⟨(E g).symm ≪≫ F.mapIso etop ≪≫ (Local.ResidueScalarIso.localResidueRestrictionIso γ).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
