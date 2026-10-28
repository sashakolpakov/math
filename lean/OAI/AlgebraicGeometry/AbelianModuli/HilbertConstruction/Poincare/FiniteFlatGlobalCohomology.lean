import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FlatAffineParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CartesianGlobalExcision
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.FamilyFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction

/-! # Finite Flat Global Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite flat parameter map pulls Poincare cohomology back to the extended
zero ideal. The formula holds globally, with the actual ground-field action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincare_finiteFlat_global_cohomology
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [T.IsSeparated] [IsLocallyNoetherian T]
    (t : T ⟶ D.abelian.scheme.left) [IsFinite t] [Flat t]
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t)
    (U : D.abelian.scheme.left.Opens) (hUa : IsAffineOpen U)
    (hU : Set.range η[D.abelian.scheme].left ⊆ U) :
    let : IsAffine U.toScheme := hUa;
    let Y := t ⁻¹ᵁ U;
    let c := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b ≫ (t ≫ D.abelian.scheme.hom));
    let cY := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := Y.ι ≫ (t ≫ D.abelian.scheme.hom));
    (∀ q : ℕ, q ≠ g → IsZero
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (D.poincare.pullback a).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c g).obj (D.poincare.pullback a).sheaf) ≅
      (ModuleCat.restrictScalars cY).obj (ModuleCat.of Γ(Y.toScheme, ⊤)
        (Γ(Y.toScheme, ⊤) ⧸ (D.poincareAffineParameterIdeal U.ι).map (t ∣_ U).appTop.hom))) := by
  let f := pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom
  let Y := t ⁻¹ᵁ U
  let V := b ⁻¹ᵁ Y
  let s := t ∣_ U
  let bV := b ∣_ Y
  have : IsAffine U.toScheme := hUa
  have : IsAffine Y.toScheme := hUa.preimage t
  have : Flat s := MorphismProperty.of_isPullback (P := @Flat)
    (isPullback_morphismRestrict t U).flip inferInstance
  have hts : s ≫ U.ι = Y.ι ≫ t := (isPullback_morphismRestrict t U).w
  have HF : IsPullback (V.ι ≫ a) bV f (s ≫ U.ι) := by
    rw [hts]
    exact ((isPullback_morphismRestrict b Y).paste_vert H.flip).flip
  let α := Cartesian.FamilyFactorization.cartesianFamilyFactorMap f U.ι s HF
  let a₀ := pullback.fst f U.ι
  let b₀ := pullback.snd f U.ι
  have H₀ : IsPullback a₀ b₀ f U.ι := IsPullback.of_hasPullback f U.ι
  have H' : IsPullback α bV b₀ s := Cartesian.FamilyFactorization.cartesianFamilyFactorMap_isPullback f U.ι s HF
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincare_flatAffineParameter_cohomology D hg hN hNk U.ι H₀ s H'
  have hα : α ≫ a₀ = V.ι ≫ a := Cartesian.FamilyFactorization.cartesianFamilyFactorMap_fst f U.ι s HF
  let L := D.poincare.pullback a
  let LV := D.poincare.pullback (α ≫ a₀)
  let eL : L.sheaf.restrict V.ι ≅ LV.sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.sheaf ≪≫
      (Scheme.Modules.pullbackComp V.ι a).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr hα.symm).app D.poincare.sheaf
  let c := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b ≫ (t ≫ D.abelian.scheme.hom))
  let cY := HilbertConstruction.Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := Y.ι ≫ (t ≫ D.abelian.scheme.hom))
  have hY : t ⁻¹' Set.range η[D.abelian.scheme].left ⊆ Y := fun _ hx => hU hx
  have hbase : V.ι ≫ (b ≫ (t ≫ D.abelian.scheme.hom)) =
      bV ≫ (Y.ι ≫ (t ≫ D.abelian.scheme.hom)) := by
    rw [← Category.assoc, ← (isPullback_morphismRestrict b Y).w, Category.assoc]
  have hc : V.ι.appTop.hom.comp c = bV.appTop.hom.comp cY := by
    ext r
    exact congrArg (fun k => k.appTop ((Scheme.ΓSpecIso (.of K)).inv r)) hbase
  let E (q : ℕ) : (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj L.sheaf ≅
      (ModuleCat.restrictScalars cY).obj
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor bV.appTop.hom q).obj LV.sheaf) :=
    D.poincareCartesianGlobalOpenCoefficientIso H c Y hY q ≪≫
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (V.ι.appTop.hom.comp c) q).mapIso eL ≪≫
      CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hc LV.sheaf q ≪≫
      (CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso cY bV.appTop.hom LV.sheaf q).symm
  exact ⟨fun q hq => (Functor.map_isZero (ModuleCat.restrictScalars cY) (hvan q hq)).of_iso (E q),
    ⟨E g ≪≫ (ModuleCat.restrictScalars cY).mapIso etop⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
