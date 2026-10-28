import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

/-! # Section Unit Zero Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionUnitZeroLocus

noncomputable section

/-! An invertibility condition together with simultaneous polynomial equations has an actual relative representing scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) {ι : Type u}

def sectionUnitZeroSubfunctor (u : Γ(M.left, ⊤)) (s : ι → Γ(M.left, ⊤)) : Subfunctor (yoneda.obj M) where
  obj T := {x | IsUnit (x.left.appTop u) ∧ ∀ i, x.left.appTop (s i) = 0}
  map a x hx := by
    refine ⟨hx.1.map a.unop.left.appTop.hom, ?_⟩
    intro i
    change a.unop.left.appTop (x.left.appTop (s i)) = 0
    rw [hx.2 i, map_zero]

theorem section_unit_zero_locus (u : Γ(M.left, ⊤)) (s : ι → Γ(M.left, ⊤)) :
    ∃ (U : Over S) (j : U ⟶ M), IsOpenImmersion j.left ∧
      ∃ (Z : Over S) (k : Z ⟶ U), IsClosedImmersion k.left ∧
        ∀ (T : Over S) (x : T ⟶ M),
          (IsUnit (x.left.appTop u) ∧ ∀ i, x.left.appTop (s i) = 0) ↔
            ∃! y : T ⟶ Z, y ≫ (k ≫ j) = x := by
  obtain ⟨U, j, hj, hU⟩ := Relative.UnitLocus.relative_unit_locus M u
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  let sU := fun i => j.left.appTop (s i)
  obtain ⟨Z, k, hk, hZ⟩ := EquationLoci.finite_equations_closed_locus [SectionZeroLocus.sectionEquation U sU]
  let := hk
  have : Mono k := Over.mono_of_mono_left k
  have hZ' (T : Over S) (x : T ⟶ U) :
      (∀ i, x.left.appTop (sU i) = 0) ↔ ∃! y : T ⟶ Z, y ≫ k = x :=
    (SectionZeroLocus.sectionEquation_satisfies U sU x).symm.trans (hZ T x)
  refine ⟨U, j, hj, Z, k, hk, ?_⟩
  intro T x
  constructor
  · rintro ⟨hunit, hzero⟩
    obtain ⟨y, hy, _⟩ := (hU T x).mp hunit
    have hyzero : ∀ i, y.left.appTop (sU i) = 0 := by
      intro i
      change (y ≫ j).left.appTop (s i) = 0
      rw [hy]
      exact hzero i
    obtain ⟨z, hz, _⟩ := (hZ' T y).mp hyzero
    have hzcomp : z ≫ (k ≫ j) = x := by rw [← Category.assoc, hz, hy]
    exact ⟨z, hzcomp, fun w hw => (cancel_mono (k ≫ j)).mp (hw.trans hzcomp.symm)⟩
  · rintro ⟨z, hz, _⟩
    have hy : (z ≫ k) ≫ j = x := (Category.assoc _ _ _).trans hz
    refine ⟨(hU T x).mpr ⟨z ≫ k, hy, fun y hy' => (cancel_mono j).mp (hy'.trans hy.symm)⟩, ?_⟩
    have hzero := (hZ' T (z ≫ k)).mpr ⟨z, rfl, fun y hy' => (cancel_mono k).mp hy'⟩
    intro i
    rw [← hy]
    exact hzero i

theorem section_unit_zero_locus_representable (u : Γ(M.left, ⊤)) (s : ι → Γ(M.left, ⊤)) :
    ∃ (U : Over S) (j : U ⟶ M), IsOpenImmersion j.left ∧
      ∃ (Z : Over S) (k : Z ⟶ U), IsClosedImmersion k.left ∧
        ∃ e : yoneda.obj Z ≅ (sectionUnitZeroSubfunctor M u s).toFunctor,
          e.hom ≫ (sectionUnitZeroSubfunctor M u s).ι = yoneda.map (k ≫ j) := by
  obtain ⟨U, j, hj, Z, k, hk, hZ⟩ := section_unit_zero_locus M u s
  let := hj
  let := hk
  have : Mono j := Over.mono_of_mono_left j
  have : Mono k := Over.mono_of_mono_left k
  let t : yoneda.obj Z ⟶ (sectionUnitZeroSubfunctor M u s).toFunctor :=
    { app := fun T => ↾fun y => ⟨y ≫ (k ≫ j), (hZ T.unop (y ≫ (k ≫ j))).mpr
        ⟨y, rfl, fun z hz => (cancel_mono (k ≫ j)).mp hz⟩⟩
      naturality := by
        intro T V a
        apply ConcreteCategory.hom_ext
        intro y
        exact Subtype.ext (Category.assoc _ _ _) }
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).mpr
    intro T
    apply (isIso_iff_bijective (t.app T)).mpr
    constructor
    · intro y z h
      exact (cancel_mono (k ≫ j)).mp (congrArg Subtype.val h)
    · intro x
      obtain ⟨y, hy, _⟩ := (hZ T.unop x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨U, j, hj, Z, k, hk, asIso t, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionUnitZeroLocus
