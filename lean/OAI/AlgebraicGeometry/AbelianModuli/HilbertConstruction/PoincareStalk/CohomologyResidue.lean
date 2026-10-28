import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.TopResidue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.TopCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.TruncatedModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AllDegreeComparison

/-! # Cohomology Residue -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The cohomology of the actual Poincare family over the dual zero stalk is concentrated in degree g, where it is one copy of the residue field. The finite free model used in the proof is constructed from the geometry. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_coefficientCohomology_residue
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom;
    let b := pullback.snd p D.poincareZeroStalkParameterMap;
    let L := D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap);
    let R := Γ(D.poincareZeroStalkScheme, ⊤);
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom g).obj L.sheaf) ≅
      ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  dsimp only
  let p := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let t := D.poincareZeroStalkParameterMap
  let P := CategoryTheory.Limits.pullback p t
  let a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left := pullback.fst p t
  let b : P ⟶ D.poincareZeroStalkScheme := pullback.snd p t
  let H : IsPullback a b p t := IsPullback.of_hasPullback p t
  let L := D.poincare.pullback a
  have : IsProper A.abelian.scheme.hom := A.abelian.proper
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip inferInstance
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  obtain ⟨k, U, hU, ha, he, C, φ, Q, hφ, hbound, hfin, hfree, ht, _, _⟩ :=
    A.poincareZeroStalk_exists_dimension_bounded_model D hN hNk
  have : QuasiIso φ := hφ
  let E (q : ℕ) : C.homology q ≅
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj L.sheaf) :=
    asIso (HomologicalComplex.homologyMap φ q) ≪≫
      OrderedCech.AllDegreeComparison.orderedCechCohomologyModuleIso b.appTop.hom L.sheaf U hU ha q
  constructor
  · intro q hq
    exact (A.poincareZeroStalk_model_cohomology_concentrated_in_dimension
      D H U hU ha he φ ht hfin hfree hN hNk q hq).of_iso (E q).symm
  · exact ⟨(E g).symm ≪≫
      D.poincareZeroStalk_model_topResidueIso H U hU ha he φ ht hfin hfree hbound Q hg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
