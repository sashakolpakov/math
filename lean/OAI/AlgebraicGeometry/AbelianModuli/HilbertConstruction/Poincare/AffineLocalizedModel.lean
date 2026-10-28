import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineStalkParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.PullbackCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.ModelLocalizationLinearity

/-! # Affine Localized Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineLocalizedModel.PolarizedAbelianWithLevel

noncomputable section

/-! The localization of an affine-neighborhood Poincare cohomology model at the actual dual zero has cohomology concentrated in degree g, equal there to one residue module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def changeBaseAlgebraLinearEquiv
    {R O : Type u} [CommRing R] [CommRing O]
    (a₁ a₂ : Algebra R O) (h : a₁ = a₂)
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (Q : ModuleCat.{u} O) (q : ℕ)
    (e : let : Algebra R O := a₁;
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R O).mapHomologicalComplex (.up ℕ)).obj C).homology q) ≃ₗ[O] Q) :
    let : Algebra R O := a₂;
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R O).mapHomologicalComplex (.up ℕ)).obj C).homology q) ≃ₗ[O] Q := by
  cases h
  exact e

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.poincareAffine_model_stalk_cohomology_residue
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
    (hx : η[D.abelian.scheme].left (IsLocalRing.closedPoint K) ∈ Set.range t)
    {P : Scheme.{u}} [P.IsSeparated]
    {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t)
    {κ : Type u} [LinearOrder κ] [Finite κ] (U : κ → P.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj
      (D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule (U i).toScheme))
    {C : CochainComplex (ModuleCat.{u} Γ(T, ⊤)) ℕ}
    (φ : C ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex b.appTop.hom (D.poincare.pullback a).sheaf U)
    (ht : ∀ (B : Type u) [AddCommGroup B] [Module Γ(T, ⊤) B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ)) :
    let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    let : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    let : Algebra Γ(T, ⊤) O := D.poincareAffineStalkAlgebra t hx;
    let CO := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor Γ(T, ⊤) O).mapHomologicalComplex (.up ℕ)).obj C;
    (∀ q : ℕ, q ≠ g → IsZero (CO.homology q)) ∧
      Nonempty (CO.homology g ≅ ModuleCat.of O (IsLocalRing.ResidueField O)) := by
  let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  let : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
    (η[D.abelian.scheme].left (IsLocalRing.closedPoint K))
  let R := Γ(T, ⊤)
  let : Algebra R O := D.poincareAffineStalkAlgebra t hx
  let m := D.poincareAffineParameterIdeal t
  let : m.IsMaximal := D.poincareAffineParameterIdeal_isMaximal_of_zero_mem t hx
  let : IsLocalization m.primeCompl O := D.poincareAffineStalk_isLocalization t hx
  let CO := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R O).mapHomologicalComplex (.up ℕ)).obj C
  let j := D.poincareAffineStalkParameterMap t hx
  let a' := pullback.fst b j
  let b' := pullback.snd b j
  let H' : IsPullback a' b' b j := IsPullback.of_hasPullback b j
  have HF : IsPullback (a' ≫ a) b' (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom)
      D.poincareZeroStalkParameterMap := by
    have h := H'.paste_horiz H
    rwa [D.poincareAffineStalkParameterMap_fac t hx] at h
  let L := D.poincare.pullback a
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap b'
  let eL : (L.pullback a').sheaf ≅ (D.poincare.pullback (a' ≫ a)).sheaf :=
    (Scheme.Modules.pullbackComp a' a).app D.poincare.sheaf
  have hcoef : HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j = algebraMap R O :=
    Affine.QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap (algebraMap R O)
  have hAlg : (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra = (inferInstance : Algebra R O) := by
    rw [hcoef]
    exact @toAlgebra_algebraMap R O _ _ (D.poincareAffineStalkAlgebra t hx)
  have hloc : let : Algebra R O := (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra; IsLocalization m.primeCompl O := by
    dsimp only
    erw [hAlg]
    infer_instance
  let E (q : ℕ) : CO.homology q ≅
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (D.poincare.pullback (a' ≫ a)).sheaf) := by
    let e : CO.homology q ≃ₗ[O]
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (L.pullback a').sheaf) := by
      have h := HilbertConstruction.Spec.ModelLocalizationLinearity.specModelCohomologyLinearEquivOfLocalization H' L U hU ha he φ ht m.primeCompl hloc q
      exact changeBaseAlgebraLinearEquiv (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j).toAlgebra
        (inferInstance : Algebra R O) hAlg C
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (L.pullback a').sheaf) q h
    exact e.toModuleIso ≪≫ (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).mapIso eL
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareZeroStalk_pullback_structuralCohomology_residue D hg hN hNk HF
  constructor
  · intro q hq
    exact (hvan q hq).of_iso (E q)
  · exact ⟨E g ≪≫ etop⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineLocalizedModel.PolarizedAbelianWithLevel
