import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert

/-! # Fixed Family Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FixedFamilyEquations

noncomputable section

section

/-! The full Presentations equations input constructs a closed parameter locus
for any finite family of relative equations, by taking zero varying
endomorphisms. The zero-tuple ambient is proved to be the base itself. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsLocallyNoetherian S]
  (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

def emptyEndomorphismTuple (T : Over S) : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A 0).obj (op T) :=
  fun i => Fin.elim0 i

theorem exists_e34_relative_equation_locus
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A) (R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A 0) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations R (emptyEndomorphismTuple A Z) ∧
      ∀ T : Over S, HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations R (emptyEndomorphismTuple A T) ↔
        ∃! _f : T ⟶ Z, True := by
  obtain ⟨B, L, _, ⟨M⟩⟩ := hPresentations A BA 0 (fun i => Fin.elim0 i) R
  have hend (T : Over S) : emptyEndomorphismTuple A T ∈ M.endLocus.obj (op T) :=
    (M.end_mem T _).mpr (fun i => Fin.elim0 i)
  have huniq (T : Over S) : Subsingleton (T ⟶ M.endScheme) := by
    constructor
    intro f h
    apply (M.endEquivalence.app (op T)).toEquiv.injective
    apply Subtype.ext
    exact funext (fun i => Fin.elim0 i)
  let unit : Over S := Over.mk (𝟙 S)
  let z : unit ⟶ M.endScheme :=
    M.endEquivalence.inv.app (op unit) ⟨emptyEndomorphismTuple A unit, hend unit⟩
  let q : M.endScheme ⟶ unit := Over.homMk M.endScheme.hom (by simp [unit])
  let e : M.endScheme ≅ unit :=
    { hom := q
      inv := z
      hom_inv_id := (huniq M.endScheme).elim _ _
      inv_hom_id := by
        apply Over.OverMorphism.ext
        exact z.w }
  have hiso : IsIso M.endScheme.hom :=
    inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
  let := hiso
  let := M.equations_closed
  have hclosed : IsClosedImmersion M.solutionScheme.hom := by
    rw [← M.forgetEquations.w]
    exact IsClosedImmersion.comp M.forgetEquations.left M.endScheme.hom
  have hsol (T : Over S) (v : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A 0).obj (op T)) :
      v = emptyEndomorphismTuple A T := funext (fun i => Fin.elim0 i)
  have huniv : HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations R (emptyEndomorphismTuple A M.solutionScheme) := by
    let v := M.solutionEquivalence.hom.app (op M.solutionScheme) (𝟙 M.solutionScheme)
    have hv := ((M.solution_mem M.solutionScheme v.val).mp v.property).2
    rw [hsol M.solutionScheme v.val] at hv
    exact hv
  refine ⟨M.solutionScheme, hclosed, huniv, fun T => ?_⟩
  constructor
  · intro h
    let v : M.solutionLocus.obj (op T) :=
      ⟨emptyEndomorphismTuple A T, (M.solution_mem T _).mpr ⟨fun i => Fin.elim0 i, h⟩⟩
    refine ⟨M.solutionEquivalence.inv.app (op T) v, trivial, fun f _ => ?_⟩
    apply (M.solutionEquivalence.app (op T)).toEquiv.injective
    apply Subtype.ext
    exact funext (fun i => Fin.elim0 i)
  · rintro ⟨f, _, _⟩
    let v := M.solutionEquivalence.hom.app (op T) f
    have hv := ((M.solution_mem T v.val).mp v.property).2
    rw [hsol T v.val] at hv
    exact hv

end

/-! Fixed morphism pairs give natural Presentations equations, whose closed locus
classifies their equality after every parameter base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
  {X Y : Over S}

def fixedRelativeMorphism (l : X ⟶ Y) :
    HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A 0 ⟶ HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Y where
  app T := ↾fun _ => (prod.snd : T.unop ⨯ X ⟶ X) ≫ l
  naturality {T U} a := by
    apply ConcreteCategory.hom_ext
    intro v
    change (prod.snd : U.unop ⨯ X ⟶ X) ≫ l =
      prod.map a.unop (𝟙 X) ≫ (prod.snd : T.unop ⨯ X ⟶ X) ≫ l
    rw [← Category.assoc, prod.map_snd, Category.comp_id]

variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]

def fixedFamilyMorphismEquation (l r : X ⟶ Y) : HilbertScheme.Presentations.Endomorphisms.Core.FamilyMorphismEquation (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A 0) where
  source := X
  target := Y
  flat := inferInstance
  proper := inferInstance
  finitelyPresented := inferInstance
  separated := inferInstance
  lhs := fixedRelativeMorphism A l
  rhs := fixedRelativeMorphism A r

def fixedFamilyEquations {m : ℕ} (l r : Fin m → (X ⟶ Y)) : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A 0 :=
  List.ofFn (fun i => fixedFamilyMorphismEquation A (l i) (r i))

theorem fixedFamilyEquations_satisfies_iff {m : ℕ} (l r : Fin m → (X ⟶ Y)) (T : Over S) :
    HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations (fixedFamilyEquations A l r) (emptyEndomorphismTuple A T) ↔
      ∀ i, (prod.snd : T ⨯ X ⟶ X) ≫ l i = (prod.snd : T ⨯ X ⟶ X) ≫ r i := by
  constructor
  · intro h i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact h i

variable [IsLocallyNoetherian S] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem exists_e34_fixed_relative_equation_locus
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0}) (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A)
    {m : ℕ} (l r : Fin m → (X ⟶ Y)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      (∀ i, (prod.snd : Z ⨯ X ⟶ X) ≫ l i = (prod.snd : Z ⨯ X ⟶ X) ≫ r i) ∧
      ∀ T : Over S,
        (∀ i, (prod.snd : T ⨯ X ⟶ X) ≫ l i = (prod.snd : T ⨯ X ⟶ X) ≫ r i) ↔
          ∃! _f : T ⟶ Z, True := by
  obtain ⟨Z, hZ, hU, hclass⟩ :=
    exists_e34_relative_equation_locus A hPresentations BA (fixedFamilyEquations A l r)
  exact ⟨Z, hZ, (fixedFamilyEquations_satisfies_iff A l r Z).mp hU,
    fun T => (fixedFamilyEquations_satisfies_iff A l r T).symm.trans (hclass T)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FixedFamilyEquations
