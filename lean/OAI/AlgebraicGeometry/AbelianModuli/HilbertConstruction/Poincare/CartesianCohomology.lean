import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.CoefficientPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AffineCohomologyFormula

/-! # Cartesian Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual Cartesian presentations of a Poincare family have the same coefficient cohomology. In particular the affine concentration and off-zero vanishing formulas transport to any Cartesian presentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section

def Dual.Data.DualAbelianData.poincareCartesianCohomologyIso
    {S T : Scheme.{u}} [T.IsSeparated] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
    (D : Dual.Data.DualAbelianData A) {t : T ⟶ D.abelian.scheme.left} {P : Scheme.{u}}
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t) (q : ℕ) :
    let p := pullback.fst D.abelian.scheme.hom A.scheme.hom;
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj
      (D.poincare.pullback a).sheaf ≅
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (pullback.snd p t).appTop.hom q).obj
      (D.poincare.pullback (pullback.fst p t)).sheaf := by
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let a₀ := pullback.fst p t
  let b₀ := pullback.snd p t
  let L₀ := D.poincare.pullback a₀
  let e := H.isoPullback
  have hA : IsProper A.scheme.hom := A.proper
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hA
  have : IsProper b₀ := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback p t) inferInstance
  have : (CategoryTheory.Limits.pullback p t).IsSeparated := ⟨by rw [← terminal.comp_from b₀]; infer_instance⟩
  have ha : e.hom ≫ a₀ = a := H.isoPullback_hom_fst
  have hb : e.hom ≫ b₀ = b := H.isoPullback_hom_snd
  let eL : (L₀.pullback e.hom).sheaf ≅ (D.poincare.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp e.hom a₀).app D.poincare.sheaf ≪≫
      eqToIso (congrArg (fun f : P ⟶ (D.abelian.scheme ⊗ A.scheme).left =>
        (D.poincare.pullback f).sheaf) ha)
  have hc : b.appTop.hom = e.hom.appTop.hom.comp b₀.appTop.hom := by
    ext r
    exact (ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hb) r).symm
  exact (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).mapIso eL.symm ≪≫
    CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hc (L₀.pullback e.hom).sheaf q ≪≫
    LineBundle.CoefficientPullbackIso.lineBundleCoefficientCohomologyPullbackIso e.hom b₀.appTop.hom L₀ q

theorem Dual.Data.DualAbelianData.poincareAffine_cartesian_cohomology_vanish_off_zero
    {S T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (t : T ⟶ D.abelian.scheme.left)
    (hoff : t ⁻¹' Set.range η[D.abelian.scheme].left = ∅)
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t) (q : ℕ) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj
      (D.poincare.pullback a).sheaf) :=
  (D.poincareAffine_coefficientCohomology_vanish_off_zero t hoff q).of_iso
    (D.poincareCartesianCohomologyIso H q)

end

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareAffine_cartesian_cohomology_formula
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {T : Scheme.{u}} [IsAffine T] (t : T ⟶ D.abelian.scheme.left) [IsOpenImmersion t]
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) t) :
    (∀ q : ℕ, q ≠ g → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom q).obj
      (D.poincare.pullback a).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor b.appTop.hom g).obj
      (D.poincare.pullback a).sheaf) ≅ ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⧸ D.poincareAffineParameterIdeal t)) := by
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareAffine_cohomology_formula D hg hN hNk t
  exact ⟨fun q hq => (hvan q hq).of_iso (D.poincareCartesianCohomologyIso H q),
    ⟨D.poincareCartesianCohomologyIso H g ≪≫ etop⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
