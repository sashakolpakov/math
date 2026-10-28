import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Parameters
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor

/-! # Pointed Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLift.PointedLiftParameters

noncomputable section

/-! The actual closed parameter scheme of pointed lifts of a fixed map.
Only relative Hom representations are supplied. The lift equations, their
closed locus, and its universal family are constructed. Unramifiedness
then proves uniqueness on connected test sources. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} (X Y Z : Over S)
  (q : Y ⟶ Z) (b : X ⟶ Z)
  (x₀ : ⊤_ (Over S) ⟶ X) (y₀ : ⊤_ (Over S) ⟶ Y)

def sectionAt (T : Over S) : T ⟶ T ⨯ X :=
  prod.lift (𝟙 T) (terminal.from T ≫ x₀)

@[reassoc] theorem sectionAt_naturality {T U : Over S} (f : T ⟶ U) :
    sectionAt X x₀ T ≫ prod.map f (𝟙 X) = f ≫ sectionAt X x₀ U := by
  apply prod.hom_ext
  · simp only [sectionAt, Category.assoc, prod.map_fst, prod.lift_fst_assoc,
      prod.lift_fst, Category.id_comp, Category.comp_id]
  · simp only [sectionAt, Category.assoc, prod.map_snd,
      prod.lift_snd, Category.comp_id]
    rw [← Category.assoc, terminal.comp_from]

def IsPointedLift {T : Over S} (f : T ⨯ X ⟶ Y) : Prop :=
  f ≫ q = prod.snd ≫ b ∧ sectionAt X x₀ T ≫ f = terminal.from T ≫ y₀

theorem isPointedLift_restrict {T U : Over S} (a : T ⟶ U) (f : U ⨯ X ⟶ Y)
    (hf : IsPointedLift X Y Z q b x₀ y₀ f) :
    IsPointedLift X Y Z q b x₀ y₀ (prod.map a (𝟙 X) ≫ f) := by
  constructor
  · rw [Category.assoc, hf.1, ← Category.assoc, prod.map_snd, Category.comp_id]
  · rw [← Category.assoc, sectionAt_naturality, Category.assoc, hf.2,
      ← Category.assoc, terminal.comp_from]

variable (H J : Over S)
  (eH : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Y).RepresentableBy H)
  (eJ : (HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Z).RepresentableBy J)

def universalHom : H ⨯ X ⟶ Y := eH.homEquiv (𝟙 H)

theorem classify_restrict {T : Over S} (a : T ⟶ H) :
    eH.homEquiv a = prod.map a (𝟙 X) ≫ universalHom X Y H eH := by
  exact (congrArg eH.homEquiv (Category.comp_id a)).symm.trans
    (eH.homEquiv_comp a (𝟙 H))

theorem classify_element {T U : Over S} (a : T ⟶ U) (r : U ⨯ X ⟶ Y) :
    eH.homEquiv (a ≫ eH.homEquiv.symm r) = prod.map a (𝟙 X) ≫ r :=
  (eH.homEquiv_comp a (eH.homEquiv.symm r)).trans
    (congrArg (fun v => prod.map a (𝟙 X) ≫ v) (eH.homEquiv.apply_symm_apply r))

variable [IsSeparated Y.hom] [IsSeparated J.hom]

def compositeEquation : HilbertScheme.Presentations.EquationLoci.MorphismEquation H where
  target := J
  separated := inferInstance
  lhs := eJ.homEquiv.symm (universalHom X Y H eH ≫ q)
  rhs := eJ.homEquiv.symm (prod.snd ≫ b)

def pointEquation : HilbertScheme.Presentations.EquationLoci.MorphismEquation H where
  target := Y
  separated := inferInstance
  lhs := sectionAt X x₀ H ≫ universalHom X Y H eH
  rhs := terminal.from H ≫ y₀

def equations : List (HilbertScheme.Presentations.EquationLoci.MorphismEquation H) :=
  [compositeEquation X Y Z q b H J eH eJ, pointEquation X Y x₀ y₀ H eH]

theorem satisfies_iff {T : Over S} (a : T ⟶ H) :
    HilbertScheme.Presentations.EquationLoci.Satisfies (equations X Y Z q b x₀ y₀ H J eH eJ) a ↔
      IsPointedLift X Y Z q b x₀ y₀ (eH.homEquiv a) := by
  have hc : a ≫ (compositeEquation X Y Z q b H J eH eJ).lhs =
      a ≫ (compositeEquation X Y Z q b H J eH eJ).rhs ↔
      eH.homEquiv a ≫ q = prod.snd ≫ b := by
    let c : (T ⟶ J) ≃ (T ⨯ X ⟶ Z) := eJ.homEquiv
    refine Iff.trans c.injective.eq_iff.symm ?_
    change eJ.homEquiv (a ≫ eJ.homEquiv.symm _) =
      eJ.homEquiv (a ≫ eJ.homEquiv.symm _) ↔ _
    rw [classify_element X Z J eJ, classify_element X Z J eJ,
      classify_restrict X Y H eH a]
    rw [← Category.assoc, ← Category.assoc, prod.map_snd, Category.comp_id]
    rfl
  have hp : a ≫ (pointEquation X Y x₀ y₀ H eH).lhs =
      a ≫ (pointEquation X Y x₀ y₀ H eH).rhs ↔
      sectionAt X x₀ T ≫ eH.homEquiv a = terminal.from T ≫ y₀ := by
    change a ≫ (sectionAt X x₀ H ≫ universalHom X Y H eH) =
      a ≫ (terminal.from H ≫ y₀) ↔ _
    rw [classify_restrict X Y H eH a, sectionAt_naturality_assoc,
      ← Category.assoc a (terminal.from H),
      terminal.comp_from]
  constructor
  · intro ha
    exact ⟨hc.mp (ha _ (by simp [equations])), hp.mp (ha _ (by simp [equations]))⟩
  · rintro ⟨ha, hb⟩ e he
    simp only [equations, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hc.mpr ha
    · exact hp.mpr hb

include eH eJ in
/-- Construct the closed lift locus and its actual universal pointed lift. -/
theorem exists_pointed_lift_scheme :
    ∃ (L : Over S) (j : L ⟶ H), IsClosedImmersion j.left ∧
      ∃ v : L ⨯ X ⟶ Y, IsPointedLift X Y Z q b x₀ y₀ v ∧
        (∀ (T : Over S) (f : T ⨯ X ⟶ Y), IsPointedLift X Y Z q b x₀ y₀ f ↔
          ∃! a : T ⟶ L, prod.map a (𝟙 X) ≫ v = f) := by
  obtain ⟨L, j, hj, hL⟩ := HilbertScheme.Presentations.EquationLoci.finite_equations_closed_locus
    (equations X Y Z q b x₀ y₀ H J eH eJ)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  let v : L ⨯ X ⟶ Y := eH.homEquiv j
  have hv : IsPointedLift X Y Z q b x₀ y₀ v :=
    (satisfies_iff X Y Z q b x₀ y₀ H J eH eJ j).mp ((hL L j).mpr
      ⟨𝟙 L, Category.id_comp j, fun a ha => (cancel_mono j).mp
        (ha.trans (Category.id_comp j).symm)⟩)
  refine ⟨L, j, hj, v, hv, ?_⟩
  intro T f
  have hmap (a : T ⟶ L) : prod.map a (𝟙 X) ≫ v = eH.homEquiv (a ≫ j) :=
    (eH.homEquiv_comp a j).symm
  constructor
  · intro hf
    let c : (T ⟶ H) ≃ (T ⨯ X ⟶ Y) := eH.homEquiv
    have hs := (satisfies_iff X Y Z q b x₀ y₀ H J eH eJ (eH.homEquiv.symm f)).mpr
      ((c.apply_symm_apply f).symm ▸ hf)
    obtain ⟨a, ha, hu⟩ := (hL T (eH.homEquiv.symm f)).mp hs
    refine ⟨a, ?_, ?_⟩
    · exact (hmap a).trans ((congrArg c ha).trans (c.apply_symm_apply f))
    · intro c hc
      apply hu
      exact eH.homEquiv.injective ((hmap c).symm.trans
        (hc.trans (eH.homEquiv.apply_symm_apply f).symm))
  · rintro ⟨a, rfl, _⟩
    exact isPointedLift_restrict X Y Z q b x₀ y₀ a v hv

omit [IsSeparated Y.hom] [IsSeparated J.hom] in
/-- Geometric uniqueness uses only the actual lift equations. -/
theorem unique_on_connected_source {T : Over S} [ConnectedSpace (T ⨯ X).left]
    [Nonempty T.left] [FormallyUnramified q.left] [LocallyOfFiniteType q.left]
    [IsSeparated q.left] (f g : T ⨯ X ⟶ Y)
    (hf : IsPointedLift X Y Z q b x₀ y₀ f)
    (hg : IsPointedLift X Y Z q b x₀ y₀ g) : f = g := by
  apply Over.OverMorphism.ext
  exact PointedLifts.pointed_unramified_lifts_unique q.left f.left g.left
    (congrArg Over.Hom.left (hf.1.trans hg.1.symm)) (sectionAt X x₀ T).left
    (congrArg Over.Hom.left (hf.2.trans hg.2.symm))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLift.PointedLiftParameters
