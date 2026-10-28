import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

/-! # Hom Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEquations.GroupHomEquations

noncomputable section

/-! The group-homomorphism equations form an actual closed locus inside
the relative Hom scheme. The only parameter representations used are
the two ordinary relative Hom functors supplied by Presentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

def unitAxis (T : Over S) : T ⟶ T ⨯ G := prod.lift (𝟙 T) 1

def multiplied {T : Over S} (f : T ⨯ G ⟶ G) : T ⨯ (G ⨯ G) ⟶ G :=
  prod.map (𝟙 T) (prod.fst * prod.snd : G ⨯ G ⟶ G) ≫ f

def multiplyImages {T : Over S} (f : T ⨯ G ⟶ G) : T ⨯ (G ⨯ G) ⟶ G :=
  (prod.map (𝟙 T) prod.fst ≫ f) * (prod.map (𝟙 T) prod.snd ≫ f)

def RespectsGroup {T : Over S} (f : T ⨯ G ⟶ G) : Prop :=
  unitAxis G T ≫ f = 1 ∧ multiplied G f = multiplyImages G f

theorem unitAxis_naturality {T U : Over S} (a : T ⟶ U) :
    unitAxis G T ≫ prod.map a (𝟙 G) = a ≫ unitAxis G U := by
  apply prod.hom_ext
  · simp only [unitAxis, Category.assoc, prod.map_fst, prod.lift_fst_assoc,
      prod.lift_fst, Category.id_comp, Category.comp_id]
  · simp only [unitAxis, Category.assoc, prod.map_snd,
      prod.lift_snd, Category.comp_id, MonObj.comp_one]

theorem multiplied_restrict {T U : Over S} (a : T ⟶ U) (f : U ⨯ G ⟶ G) :
    multiplied G (prod.map a (𝟙 G) ≫ f) =
      prod.map a (𝟙 (G ⨯ G)) ≫ multiplied G f := by
  simp only [multiplied, ← Category.assoc, prod.map_map, Category.id_comp, Category.comp_id]

theorem multiplyImages_restrict {T U : Over S} (a : T ⟶ U) (f : U ⨯ G ⟶ G) :
    multiplyImages G (prod.map a (𝟙 G) ≫ f) =
      prod.map a (𝟙 (G ⨯ G)) ≫ multiplyImages G f := by
  simp only [multiplyImages, MonObj.comp_mul, ← Category.assoc, prod.map_map,
    Category.id_comp, Category.comp_id]

variable (H J : Over S)
  (eH : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor G G).RepresentableBy H)
  (eJ : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor (G ⨯ G) G).RepresentableBy J)
  [hG : IsSeparated G.hom] [hJ : IsSeparated J.hom]

def universal : H ⨯ G ⟶ G := eH.homEquiv (𝟙 H)

omit [GrpObj G] hG in
theorem universal_restrict {T : Over S} (a : T ⟶ H) :
    eH.homEquiv a = prod.map a (𝟙 G) ≫ universal G H eH := by
  exact (congrArg eH.homEquiv (Category.comp_id a)).symm.trans
    (eH.homEquiv_comp a (𝟙 H))

omit [GrpObj G] hG hJ in
theorem classify_product_element {T U : Over S} (a : T ⟶ U)
    (r : U ⨯ (G ⨯ G) ⟶ G) :
    eJ.homEquiv (a ≫ eJ.homEquiv.symm r) = prod.map a (𝟙 (G ⨯ G)) ≫ r :=
  (eJ.homEquiv_comp a (eJ.homEquiv.symm r)).trans
    (congrArg (fun v => prod.map a (𝟙 (G ⨯ G)) ≫ v) (eJ.homEquiv.apply_symm_apply r))

def unitEquation : HilbertScheme.Presentations.EquationLoci.MorphismEquation H where
  target := G
  separated := inferInstance
  lhs := unitAxis G H ≫ universal G H eH
  rhs := 1

def multiplicationEquation : HilbertScheme.Presentations.EquationLoci.MorphismEquation H where
  target := J
  separated := inferInstance
  lhs := eJ.homEquiv.symm (multiplied G (universal G H eH))
  rhs := eJ.homEquiv.symm (multiplyImages G (universal G H eH))

def equations : List (HilbertScheme.Presentations.EquationLoci.MorphismEquation H) :=
  [unitEquation G H eH, multiplicationEquation G H J eH eJ]

theorem satisfies_iff {T : Over S} (a : T ⟶ H) :
    HilbertScheme.Presentations.EquationLoci.Satisfies (equations G H J eH eJ) a ↔ RespectsGroup G (eH.homEquiv a) := by
  have hu : a ≫ (unitEquation G H eH).lhs = a ≫ (unitEquation G H eH).rhs ↔
      unitAxis G T ≫ eH.homEquiv a = 1 := by
    simp only [unitEquation, universal_restrict, ← Category.assoc, unitAxis_naturality,
      MonObj.comp_one]
  have hm : a ≫ (multiplicationEquation G H J eH eJ).lhs =
      a ≫ (multiplicationEquation G H J eH eJ).rhs ↔
      multiplied G (eH.homEquiv a) = multiplyImages G (eH.homEquiv a) := by
    let c : (T ⟶ J) ≃ (T ⨯ (G ⨯ G) ⟶ G) := eJ.homEquiv
    refine Iff.trans c.injective.eq_iff.symm ?_
    change eJ.homEquiv (a ≫ eJ.homEquiv.symm _) =
      eJ.homEquiv (a ≫ eJ.homEquiv.symm _) ↔ _
    rw [classify_product_element, classify_product_element,
      universal_restrict, multiplied_restrict, multiplyImages_restrict]
    rfl
  change (∀ e ∈ [unitEquation G H eH, multiplicationEquation G H J eH eJ],
    a ≫ e.lhs = a ≫ e.rhs) ↔ _
  simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    RespectsGroup, hu, hm, forall_false, implies_true, and_true]

include eJ hG hJ in
theorem exists_closed_group_hom_locus :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧
      RespectsGroup G (eH.homEquiv j) ∧
      ∀ (T : Over S) (f : T ⨯ G ⟶ G), RespectsGroup G f →
        ∃! a : T ⟶ Z, eH.homEquiv (a ≫ j) = f := by
  obtain ⟨Z, j, hj, hZ⟩ := HilbertScheme.Presentations.EquationLoci.finite_equations_closed_locus (equations G H J eH eJ)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  have hjGroup : RespectsGroup G (eH.homEquiv j) := (satisfies_iff G H J eH eJ j).mp
    ((hZ Z j).mpr ⟨𝟙 Z, Category.id_comp j, fun a ha =>
      (cancel_mono j).mp (ha.trans (Category.id_comp j).symm)⟩)
  refine ⟨Z, j, hj, hjGroup, ?_⟩
  intro T f hf
  let p : T ⟶ H := eH.homEquiv.symm f
  have hp : eH.homEquiv p = f := eH.homEquiv.apply_symm_apply f
  obtain ⟨a, ha, huniq⟩ := (hZ T p).mp
    ((satisfies_iff G H J eH eJ p).mpr (hp.symm ▸ hf))
  refine ⟨a, (congrArg eH.homEquiv ha).trans hp, ?_⟩
  intro b hb
  exact huniq b (eH.homEquiv.injective (hb.trans hp.symm))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEquations.GroupHomEquations
