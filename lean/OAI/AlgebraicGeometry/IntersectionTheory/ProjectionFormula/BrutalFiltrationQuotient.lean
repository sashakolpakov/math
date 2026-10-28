import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SplitSequence
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! # Brutal Filtration Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient

noncomputable section

/-! Adjacent stages of the tail filtration form a degreewise split exact
sequence whose quotient is the single newly included degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration

variable (R : Type) [CommRing R] (A : CochainComplex (ModuleCat.{0} R) ℤ) (p : ℤ)

def stageMap : BrutalFiltration.complex R A (p : EInt) ⟶ BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt) :=
  BrutalFiltration.inclusion R A (WithBotTop.coe_le_coe.mpr (by omega))

def quotient : CochainComplex (ModuleCat.{0} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{0} R) (.up ℤ) (-(p + 1))).obj (A.X (-(p + 1)))

def projection : BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt) ⟶ BrutalFiltrationQuotient.quotient R A p :=
  HomologicalComplex.mkHomToSingle ((BrutalFiltration.toComplex R A ((p + 1 : ℤ) : EInt)).f (-(p + 1))) (by
    intro i hi
    have hz : IsZero ((BrutalFiltration.complex R A ((p + 1 : ℤ) : EInt)).X i) :=
      BrutalFiltration.zero_below R A _ i (by
        rw [WithBotTop.coe_le_coe]
        change i + 1 = -(p + 1) at hi
        omega)
    exact hz.eq_of_src _ _)

theorem stageMap_projection : stageMap R A p ≫ projection R A p = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = -(p + 1)
  · subst n
    exact (BrutalFiltration.zero_below R A (p : EInt) (-(p + 1)) (by
      rw [WithBotTop.coe_le_coe]
      omega)).eq_of_src _ _
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(p + 1))
      (A.X (-(p + 1))) n hn).eq_of_tgt _ _

def sequence : ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ) :=
  ShortComplex.mk (stageMap R A p) (projection R A p) (stageMap_projection R A p)

theorem projection_boundary_isIso : IsIso ((projection R A p).f (-(p + 1))) := by
  let := BrutalFiltration.toComplex_f_isIso R A ((p + 1 : ℤ) : EInt) (-(p + 1)) (by
    rw [WithBotTop.coe_le_coe]
    omega)
  dsimp only [projection]
  rw [HomologicalComplex.mkHomToSingle_f]
  infer_instance

theorem stageMap_isIso_away (n : ℤ) (hn : n ≠ -(p + 1)) : IsIso ((stageMap R A p).f n) := by
  by_cases hp : ((-n : ℤ) : EInt) ≤ (p : EInt)
  · exact BrutalFiltration.inclusion_f_isIso R A _ n hp
  · have hq : ¬ ((-n : ℤ) : EInt) ≤ ((p + 1 : ℤ) : EInt) := by
      rw [WithBotTop.coe_le_coe] at hp ⊢
      omega
    exact (BrutalFiltration.zero_below R A (p : EInt) n hp).isIso
      (BrutalFiltration.zero_below R A ((p + 1 : ℤ) : EInt) n hq) _

def splitting (n : ℤ) :
    ((sequence R A p).map (HomologicalComplex.eval _ _ n)).Splitting := by
  by_cases hn : n = -(p + 1)
  · subst n
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _
      (BrutalFiltration.zero_below R A (p : EInt) (-(p + 1)) (by rw [WithBotTop.coe_le_coe]; omega))
      (projection_boundary_isIso R A p)
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (stageMap_isIso_away R A p n hn)
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) (-(p + 1)) (A.X (-(p + 1))) n hn)

theorem shortExact : (sequence R A p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (splitting R A p n).shortExact)

theorem triangle_distinguished :
    trianglehOfDegreewiseSplit (sequence R A p) (splitting R A p) ∈
      distTriang (HomotopyCategory (ModuleCat.{0} R) (.up ℤ)) :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).mpr
    ⟨sequence R A p, splitting R A p, ⟨Iso.refl _⟩⟩

def coneIso :
    (HomotopyCategory.quotient _ _).obj (mappingCone (stageMap R A p)) ≅
      (HomotopyCategory.quotient _ _).obj (BrutalFiltrationQuotient.quotient R A p) :=
  CategoryTheory.Pretriangulated.Triangle.π₃.mapIso
    (CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished (stageMap R A p))
      (triangle_distinguished R A p) (Iso.refl _) (Iso.refl _) (by
        change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
        rw [Category.comp_id, Category.id_comp]
        rfl))

def tensorConeHomologyIso (K : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    ((Tensor.Homotopy.complexFunctor R K).obj (mappingCone (stageMap R A p))).homology n ≅
      ((Tensor.Homotopy.complexFunctor R K).obj (BrutalFiltrationQuotient.quotient R A p)).homology n := by
  let := Tensor.SplitSequence.quasiIso_descShortComplex R K (sequence R A p) (splitting R A p)
  exact asIso (HomologicalComplex.homologyMap
    ((Tensor.Homotopy.complexFunctor R K).map (mappingCone.descShortComplex (sequence R A p))) n)

theorem tensorConeHomologyIso_hom (K : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    (tensorConeHomologyIso R A p K n).hom = HomologicalComplex.homologyMap
      ((Tensor.Homotopy.complexFunctor R K).map (mappingCone.descShortComplex (sequence R A p))) n := rfl

def relativeTermIso (K : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℤ) :
    ((Tensor.SpectralObject.abelian R K (BrutalFiltration.filtration R A)).H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (p : EInt) ≤ ((p + 1 : ℤ) : EInt) from WithBotTop.coe_le_coe.mpr (by omega)))) ≅
    ((Tensor.Homotopy.complexFunctor R K).obj (BrutalFiltrationQuotient.quotient R A p)).homology n :=
  Tensor.SpectralObject.termIso R K (BrutalFiltration.filtration R A) _ n ≪≫ tensorConeHomologyIso R A p K n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient
