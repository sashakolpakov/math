import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Equation Loci -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci

noncomputable section

/-!
Closed loci of finite systems of actual morphism equations into separated
schemes, together with the representing natural equivalence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S)

/-- One actual pair of comparison morphisms into a separated S-scheme. -/
structure MorphismEquation where
  target : Over S
  separated : IsSeparated target.hom
  lhs : M ⟶ target
  rhs : M ⟶ target

variable {M}

/-- Satisfaction of all equations after pullback along a parameter point. -/
def Satisfies (equations : List (MorphismEquation M))
    {T : Over S} (x : T ⟶ M) : Prop :=
  ∀ e ∈ equations, x ≫ e.lhs = x ≫ e.rhs

/-- The solution condition is compatible with arbitrary changes of parameters. -/
def equationSubfunctor (equations : List (MorphismEquation M)) :
    Subfunctor (yoneda.obj M) where
  obj T := {x | Satisfies equations x}
  map a x hx := by
    intro e he
    change (a.unop ≫ x) ≫ e.lhs = (a.unop ≫ x) ≫ e.rhs
    rw [Category.assoc, Category.assoc, hx e he]

/-- A finite system of actual morphism equations is represented by a closed
subscheme. The comparison morphisms themselves are data, not assumed loci. -/
theorem finite_equations_closed_locus
    (equations : List (MorphismEquation M)) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ M),
        Satisfies equations x ↔ ∃! y : T ⟶ Z, y ≫ j = x := by
  induction equations with
  | nil =>
      refine ⟨M, 𝟙 M, ?_, ?_⟩
      · change IsClosedImmersion (𝟙 M.left)
        infer_instance
      intro T x
      constructor
      · intro _
        exact ⟨x, Category.comp_id x, fun y hy => (Category.comp_id y).symm.trans hy⟩
      · intro _ e he
        cases he
  | cons e equations ih =>
      obtain ⟨Z, j, hj, hZ⟩ := ih
      let := hj
      have : Mono j := Over.mono_of_mono_left j
      let := e.separated
      let f : Z ⟶ e.target := j ≫ e.lhs
      let g : Z ⟶ e.target := j ≫ e.rhs
      let k : equalizer f g ⟶ Z := equalizer.ι f g
      have hk : IsClosedImmersion k.left := inferInstance
      let := hk
      refine ⟨equalizer f g, k ≫ j, ?_, ?_⟩
      · change IsClosedImmersion (k.left ≫ j.left)
        infer_instance
      · intro T x
        constructor
        · intro hx
          have hxTail : Satisfies equations x :=
            fun d hd => hx d (List.mem_cons_of_mem e hd)
          obtain ⟨y, hy, _⟩ := (hZ T x).mp hxTail
          have hyEq : y ≫ f = y ≫ g := by
            change y ≫ (j ≫ e.lhs) = y ≫ (j ≫ e.rhs)
            rw [← Category.assoc, ← Category.assoc, hy]
            exact hx e (List.mem_cons_self)
          refine ⟨equalizer.lift y hyEq, ?_, ?_⟩
          · change equalizer.lift y hyEq ≫ equalizer.ι f g ≫ j = x
            rw [equalizer.lift_ι_assoc, hy]
          · intro z hz
            apply (cancel_mono (k ≫ j)).mp
            exact hz.trans (by
              change x = equalizer.lift y hyEq ≫ equalizer.ι f g ≫ j
              rw [equalizer.lift_ι_assoc, hy])
        · rintro ⟨y, hy, _⟩
          have hyTail : Satisfies equations x := by
            apply (hZ T x).mpr
            refine ⟨y ≫ k, ?_, ?_⟩
            · exact (Category.assoc _ _ _).trans hy
            · intro z hz
              apply (cancel_mono j).mp
              exact hz.trans ((Category.assoc _ _ _).trans hy).symm
          intro d hd
          rcases List.mem_cons.mp hd with hd | hd
          · subst d
            rw [← hy]
            change (y ≫ (equalizer.ι f g ≫ j)) ≫ e.lhs =
              (y ≫ (equalizer.ι f g ≫ j)) ≫ e.rhs
            simp only [Category.assoc]
            exact congrArg (fun h => y ≫ h) (equalizer.condition f g)
          · exact hyTail d hd

/-- The finite-equation construction represents the whole solution functor,
with its inclusion into the parameter functor. -/
theorem finite_equations_representable
    (equations : List (MorphismEquation M)) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∃ e : yoneda.obj Z ≅ (equationSubfunctor equations).toFunctor,
        e.hom ≫ (equationSubfunctor equations).ι = yoneda.map j := by
  obtain ⟨Z, j, hj, hZ⟩ := finite_equations_closed_locus equations
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  let t : yoneda.obj Z ⟶ (equationSubfunctor equations).toFunctor :=
    { app := fun T => ↾fun y =>
        ⟨y ≫ j, (hZ T.unop (y ≫ j)).mpr
          ⟨y, rfl, fun z hz => (cancel_mono j).mp hz⟩⟩
      naturality := by
        intro T U a
        ext y
        apply Subtype.ext
        exact Category.assoc _ _ _ }
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).mpr
    intro T
    apply (isIso_iff_bijective (t.app T)).mpr
    constructor
    · intro y z h
      apply (cancel_mono j).mp
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨y, hy, _⟩ := (hZ T.unop x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
  refine ⟨Z, j, hj, asIso t, ?_⟩
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci
