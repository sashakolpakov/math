import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareStalk.StructuralCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence

/-! # Pullback Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual stalk-family cohomology computation is invariant under its Cartesian presentation. This compares both the pulled-back Poincare bundle and its structural coefficient map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section

def Dual.Data.DualAbelianData.poincareZeroStalkPullbackCohomologyIso
    {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) {P : Scheme.{u}}
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ D.poincareZeroStalkScheme}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) D.poincareZeroStalkParameterMap)
    (q : ℕ) :
    let p := pullback.fst D.abelian.scheme.hom A.scheme.hom;
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).obj
      (D.poincare.pullback a).sheaf) ≅
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (pullback.snd p D.poincareZeroStalkParameterMap)) q).obj
        (D.poincare.pullback (pullback.fst p D.poincareZeroStalkParameterMap)).sheaf) := by
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let t := D.poincareZeroStalkParameterMap
  let P₀ := CategoryTheory.Limits.pullback p t
  let a₀ := pullback.fst p t
  let b₀ := pullback.snd p t
  let L₀ := D.poincare.pullback a₀
  let e := H.isoPullback
  have hA : IsProper A.scheme.hom := A.proper
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hA
  have : IsProper b₀ := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback p t) inferInstance
  have : P₀.IsSeparated := ⟨by rw [← terminal.comp_from b₀]; infer_instance⟩
  have ha : e.hom ≫ a₀ = a := H.isoPullback_hom_fst
  have hb : e.hom ≫ b₀ = b := H.isoPullback_hom_snd
  let eL : (L₀.pullback e.hom).sheaf ≅ (D.poincare.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp e.hom a₀).app D.poincare.sheaf ≪≫
      eqToIso (congrArg (fun f : P ⟶ (D.abelian.scheme ⊗ A.scheme).left =>
        (D.poincare.pullback f).sheaf) ha)
  exact (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).mapIso eL.symm ≪≫
    CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr (congrArg Coefficient.ModulePresheaf.schemeCoefficientMap hb).symm
      (L₀.pullback e.hom).sheaf q ≪≫
    CohomologyPullbackIso.lineBundleCohomologyPullbackIso e.hom b₀ L₀ q

end

theorem PolarizationData.PolarizedAbelianWithFullLevel.poincareZeroStalk_pullback_structuralCohomology_residue
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) (D : Dual.Data.DualAbelianData A.abelian)
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.abelian.scheme).left}
    {b : P ⟶ D.poincareZeroStalkScheme}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.abelian.scheme.hom) D.poincareZeroStalkParameterMap) :
    let O := D.abelian.scheme.left.presheaf.stalk (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    letI : IsLocalRing O := D.abelian.scheme.left.toLocallyRingedSpace.isLocalRing
      (η[D.abelian.scheme].left (IsLocalRing.closedPoint K));
    (∀ q : ℕ, q ≠ g → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).obj (D.poincare.pullback a).sheaf)) ∧
    Nonempty (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap b) g).obj
      (D.poincare.pullback a).sheaf) ≅ ModuleCat.of O (IsLocalRing.ResidueField O)) := by
  obtain ⟨hvan, ⟨etop⟩⟩ := A.poincareZeroStalk_structuralCohomology_residue D hg hN hNk
  constructor
  · intro q hq
    exact (hvan q hq).of_iso (D.poincareZeroStalkPullbackCohomologyIso H q)
  · exact ⟨D.poincareZeroStalkPullbackCohomologyIso H g ≪≫ etop⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
