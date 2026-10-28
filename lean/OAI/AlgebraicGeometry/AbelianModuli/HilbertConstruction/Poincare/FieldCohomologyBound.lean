import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.StructureCohomologyFieldBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FieldFiberCohomology

/-! # Field Cohomology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Poincare family of a polarized abelian scheme has no field-fiber cohomology above dimension g. Away from zero all cohomology vanishes; at zero the normalized bundle is trivial and the sharp structure-sheaf bound applies. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (D : Dual.Data.DualAbelianData A.abelian)
variable (c : Spec (.of K) ⟶ S)
variable (x : (Over.map c).obj (𝟙_ (Over (Spec (.of K)))) ⟶ D.abelian.scheme)

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareFieldSpecialization_cohomology_vanish_above_dimension
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : g < q) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      (D.poincare.pullback (D.poincareFieldSpecializationMap c x)).sheaf q) := by
  by_cases hx : x = 1
  · subst x
    have hz : D.poincareFieldSpecializationPoint c 1 = 1 := by
      exact (D.abelian.baseChangePointsMulEquiv c (𝟙_ (Over (Spec (.of K))))).symm.map_one
    let B := A.pullback c
    have hB : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (Line.Bundles.structureModule B.abelian.scheme.left) q) :=
      ModuleCat.subsingleton_of_isZero
        (B.structure_cohomology_vanish_above_dimension hN hNk q hq)
    let ep : ((D.pullback c).poincarePointBundle
        (D.poincareFieldSpecializationPoint c 1)).sheaf ≅ Line.Bundles.structureModule B.abelian.scheme.left := by
      rw [hz]
      exact (D.pullback c).poincarePointBundle_oneIso
    let eL := (D.poincareFieldSpecializationBundleIso c 1).symm ≪≫ ep
    let eH := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor B.abelian.scheme.left q).mapIso eL
    have hi : Function.Injective eH.hom :=
      (AddCommGrpCat.mono_iff_injective eH.hom).mp inferInstance
    exact ⟨fun v w => hi (hB.elim _ _)⟩
  · exact D.poincareFieldSpecialization_cohomology_vanish c x hx q

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareFieldFiber_cohomology_vanish_above_dimension
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left}
    {b : P ⟶ Spec (.of K)}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) x.left)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : g < q) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincare.pullback a).sheaf q) := by
  have hA : IsProper A.abelian.scheme.hom := A.abelian.proper
  have hfst : IsProper (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback D.abelian.scheme.hom A.abelian.scheme.hom).flip hA
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H hfst
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  let e := D.poincareFieldFiberIso c x H
  let L := D.poincare.pullback a
  let eL : (L.pullback e.hom).sheaf ≅
      (D.poincare.pullback (D.poincareFieldSpecializationMap c x)).sheaf :=
    (Scheme.Modules.pullbackComp e.hom a).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (D.poincareFieldFiberIso_hom_map c x H)).app D.poincare.sheaf
  have hzero := A.poincareFieldSpecialization_cohomology_vanish_above_dimension D c x hN hNk q hq
  let eC := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.abelian.pullback c).scheme.left q).mapIso eL
  have hi : Function.Injective eC.hom :=
    (AddCommGrpCat.mono_iff_injective eC.hom).mp inferInstance
  have hs : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback e.hom).sheaf q) :=
    ⟨fun v w => hi (hzero.elim _ _)⟩
  let h := CohomologyPullbackIso.lineBundleCohomologyPullbackIso e.hom b L q
  have hj : Function.Injective h.inv := (ModuleCat.mono_iff_injective h.inv).mp inferInstance
  exact ⟨fun v w => hj (hs.elim _ _)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
