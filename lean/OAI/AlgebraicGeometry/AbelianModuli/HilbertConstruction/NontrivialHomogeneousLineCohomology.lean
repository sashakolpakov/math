import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineSectionTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldExternalFirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyRetraction

/-! # Nontrivial Homogeneous Line Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialHomogeneousLineCohomology

noncomputable section

/-! Every nontrivial homogeneous line bundle on an abelian variety over
an algebraically closed field has zero cohomology in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L))
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule A.scheme.left))

include hL hne in
theorem nontrivialHomogeneousLine_section_eq_zero
    (s : Line.Bundles.structureModule A.scheme.left ⟶ L.sheaf) : s = 0 := by
  classical
  by_contra hs
  exact hne (Homogeneous.LineSectionTriviality.homogeneousLine_trivial_of_nonzero_section A L hL s hs)

include hL hne in
theorem nontrivialHomogeneousLine_sections_subsingleton : Subsingleton Γ(L.sheaf, ⊤) := by
  constructor
  intro z w
  apply (Global.Sections.moduleSectionHomEquiv L.sheaf).symm.injective
  exact (nontrivialHomogeneousLine_section_eq_zero A L hL hne
    ((Global.Sections.moduleSectionHomEquiv L.sheaf).symm z)).trans
      (nontrivialHomogeneousLine_section_eq_zero A L hL hne
        ((Global.Sections.moduleSectionHomEquiv L.sheaf).symm w)).symm

def homogeneousLine_externalSquareCohomologyMap (n : ℕ) :
    Zariski.Cohomology.ZariskiCohomology.H L.sheaf n →+
      Zariski.Cohomology.ZariskiCohomology.H (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme) L L).sheaf n :=
  ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.scheme ⊗ A.scheme).left n).map
    (Homogeneous.LineMultiplication.homogeneousLine_additionIso A L hL).hom).hom.comp
      (Zariski.CohomologyPullbackMap.ZariskiCohomology.pullbackMap
        (fst A.scheme A.scheme * snd A.scheme A.scheme).left L.sheaf n)

omit [IsAlgClosed K] in
theorem homogeneousLine_externalSquareCohomologyMap_injective (n : ℕ) :
    Function.Injective (homogeneousLine_externalSquareCohomologyMap A L hL n) := by
  let m := fst A.scheme A.scheme * snd A.scheme A.scheme
  let s := lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)
  have hs₀ : s ≫ m = 𝟙 A.scheme := by
    change lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) ≫
      (fst A.scheme A.scheme * snd A.scheme A.scheme) = 𝟙 A.scheme
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_one]
  have hs : s.left ≫ m.left = 𝟙 A.scheme.left := congrArg Over.Hom.left hs₀
  have hp := Zariski.CohomologyRetraction.ZariskiCohomology.pullbackMap_injective_of_section m.left s.left hs L.sheaf n
  have he := (ConcreteCategory.bijective_of_isIso
    ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.scheme ⊗ A.scheme).left n).map
      (Homogeneous.LineMultiplication.homogeneousLine_additionIso A L hL).hom)).injective
  exact he.comp hp

include hL hne in
theorem nontrivialHomogeneousLine_cohomology_vanish (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf q) := by
  have hsections := nontrivialHomogeneousLine_sections_subsingleton A L hL hne
  have H : IsPullback (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left
      A.scheme.hom A.scheme.hom := IsPullback.of_hasPullback A.scheme.hom A.scheme.hom
  induction q using Nat.strong_induction_on with
  | h q ih =>
    cases q with
    | zero =>
      constructor
      intro x y
      apply (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections L.sheaf).injective
      exact @Subsingleton.elim _ hsections _ _
    | succ n =>
      have hprod : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
          (Graph.ExternalTensorBundle.externalTensorBundle (A := A.scheme) (B := A.scheme) L L).sheaf (n + 1)) :=
        Proper.FieldExternalFirstCohomology.properFieldExternalTensor_firstCohomology_vanish H L L n ih hsections
      constructor
      intro x y
      apply homogeneousLine_externalSquareCohomologyMap_injective A L hL (n + 1)
      exact @Subsingleton.elim _ hprod _ _

include hL hne in
theorem nontrivialHomogeneousLine_cohomology_isZero (q : ℕ) :
    IsZero ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor A.scheme.left q).obj L.sheaf) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact nontrivialHomogeneousLine_cohomology_vanish A L hL hne q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NontrivialHomogeneousLineCohomology
