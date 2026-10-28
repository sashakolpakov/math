import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveEquationLoci
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EquationBaseChange

/-! # Projective Fixed Equation Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveFixedEquationLocus

noncomputable section

/-! Fixed morphism equations with a projective source have a closed
base locus on all tests. This uses the proved projective equation
theorem directly, with no Hilbert/Hom or equation-locus input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveEquationLoci.Core

variable {S : Scheme.{0}} {X Y : Over S}

def fixedProjectiveMorphism (l : X ⟶ Y) :
    yoneda.obj (Over.mk (𝟙 S)) ⟶ HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Y where
  app T := ↾fun _ => (prod.snd : T.unop ⨯ X ⟶ X) ≫ l
  naturality {T U} a := by
    apply ConcreteCategory.hom_ext
    intro v
    change (prod.snd : U.unop ⨯ X ⟶ X) ≫ l =
      prod.map a.unop (𝟙 X) ≫ (prod.snd : T.unop ⨯ X ⟶ X) ≫ l
    rw [← Category.assoc, prod.map_snd, Category.comp_id]

variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
  [IsSeparated Y.hom]

def fixedProjectiveEquation (l r : X ⟶ Y) :
    HilbertScheme.Presentations.Endomorphisms.Core.FamilyMorphismEquation (yoneda.obj (Over.mk (𝟙 S))) where
  source := X
  target := Y
  flat := inferInstance
  proper := inferInstance
  finitelyPresented := inferInstance
  separated := inferInstance
  lhs := fixedProjectiveMorphism l
  rhs := fixedProjectiveMorphism r

theorem exists_projective_fixed_pullback_equation_locus
    [IsLocallyNoetherian S] (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)
    {m : ℕ} (l r : Fin m → (X ⟶ Y)) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧
      (∀ i, (Over.pullback Z.hom).map (l i) = (Over.pullback Z.hom).map (r i)) ∧
      ∀ T : Over S,
        (∀ i, (Over.pullback T.hom).map (l i) = (Over.pullback T.hom).map (r i)) ↔
          ∃! _f : T ⟶ Z, True := by
  let M : Over S := Over.mk (𝟙 S)
  let : IsLocallyNoetherian M.left := inferInstanceAs (IsLocallyNoetherian S)
  let R := List.ofFn (fun i => fixedProjectiveEquation (l i) (r i))
  have hR : ∀ q ∈ R, Nonempty (HilbertScheme.Presentations.Has.Core.ProjectivePresentation q.source) := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨B⟩
  obtain ⟨Z, j, hj, htest⟩ := HilbertScheme.Presentations.Finite.ProjectiveEquationLoci.Core.finite_projective_equations_closed_lifts R hR (𝟙 (yoneda.obj M))
  let : IsClosedImmersion j.left := hj
  change ∀ (T : Over S) (x : T ⟶ M), HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations R x ↔
    ∃! y : T ⟶ Z, y ≫ j = x at htest
  have hw : (show Z.left ⟶ S from j.left) = Z.hom := by
    calc
      (show Z.left ⟶ S from j.left) = (show Z.left ⟶ S from j.left) ≫ 𝟙 S :=
        (Category.comp_id _).symm
      _ = Z.hom := j.w
  have hZ : IsClosedImmersion Z.hom := by
    exact hw ▸ hj
  let x (T : Over S) : T ⟶ M := Over.homMk T.hom (Category.comp_id _)
  have hx (T : Over S) (f : T ⟶ Z) : f ≫ j = x T := by
    apply Over.OverMorphism.ext
    change f.left ≫ (show Z.left ⟶ S from j.left) = T.hom
    rw [hw]
    exact f.w
  have heq (T : Over S) :
      (∀ i, (Over.pullback T.hom).map (l i) = (Over.pullback T.hom).map (r i)) ↔
        HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations R (x T) := by
    constructor
    · intro h q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact (PELModuli.IntegralModel.Presentations.EquationBaseChange.fixed_relative_equation_iff_pullback T (l i) (r i)).mpr (h i)
    · intro h i
      exact (PELModuli.IntegralModel.Presentations.EquationBaseChange.fixed_relative_equation_iff_pullback T (l i) (r i)).mp
        (h _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hclass (T : Over S) :
      (∀ i, (Over.pullback T.hom).map (l i) = (Over.pullback T.hom).map (r i)) ↔
        ∃! _f : T ⟶ Z, True := by
    rw [heq T, htest T (x T)]
    constructor
    · rintro ⟨f, _, hf⟩
      exact ⟨f, trivial, fun q _ => hf q (hx T q)⟩
    · rintro ⟨f, _, hf⟩
      exact ⟨f, hx T f, fun q _ => hf q trivial⟩
  refine ⟨Z, hZ, (hclass Z).mpr ?_, hclass⟩
  let : IsClosedImmersion Z.hom := hZ
  let : Mono j := Over.mono_of_mono_left j
  exact ⟨𝟙 Z, trivial, fun q _ => (cancel_mono j).mp ((hx Z q).trans (hx Z (𝟙 Z)).symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveFixedEquationLocus
