import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FamilyEquationLocus

/-! # Proper Equation Loci -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProperEquationLoci.Core

noncomputable section

/-! Finite natural equations with proper flat sources are represented by
a closed parameter scheme, with their exact natural solution subfunctor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}

theorem finite_proper_equations_closed_lifts
    (R : List (Endomorphisms.Core.FamilyMorphismEquation F))
    {M : Over S} [IsLocallyNoetherian M.left] (φ : yoneda.obj M ⟶ F) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ M), Endomorphisms.Core.SatisfiesEquations R (φ.app (.op T) x) ↔
        ∃! y : T ⟶ Z, y ≫ j = x := by
  induction R generalizing M with
  | nil =>
    refine ⟨M, 𝟙 M, inferInstanceAs (IsClosedImmersion (𝟙 M.left)), ?_⟩
    intro T x
    constructor
    · intro _
      exact ⟨x, Category.comp_id x, fun y hy => by simpa only [Category.comp_id] using hy⟩
    · intro _ r hr
      cases hr
  | cons r R ih =>
    obtain ⟨Z₁, j₁, hj₁, h₁⟩ := r.proper_closed_locus φ
    let : IsClosedImmersion j₁.left := hj₁
    let : Mono j₁ := Over.mono_of_mono_left j₁
    let : IsLocallyNoetherian Z₁.left := by
      exact LocallyOfFiniteType.isLocallyNoetherian j₁.left
    obtain ⟨Z₂, j₂, hj₂, h₂⟩ := ih (yoneda.map j₁ ≫ φ)
    let : IsClosedImmersion j₂.left := hj₂
    let : Mono j₂ := Over.mono_of_mono_left j₂
    refine ⟨Z₂, j₂ ≫ j₁, inferInstanceAs (IsClosedImmersion (j₂.left ≫ j₁.left)), ?_⟩
    intro T x
    constructor
    · intro hx
      obtain ⟨y, hy, _⟩ := (h₁ T x).mp (hx r (List.mem_cons_self ..))
      have hyR : Endomorphisms.Core.SatisfiesEquations R ((yoneda.map j₁ ≫ φ).app (.op T) y) := by
        change Endomorphisms.Core.SatisfiesEquations R (φ.app (.op T) (y ≫ j₁))
        rw [hy]
        exact fun s hs => hx s (List.mem_cons_of_mem r hs)
      obtain ⟨z, hz, _⟩ := (h₂ T y).mp hyR
      have hz' : z ≫ (j₂ ≫ j₁) = x := by rw [← Category.assoc, hz, hy]
      exact ⟨z, hz', fun w hw => (cancel_mono (j₂ ≫ j₁)).mp (hw.trans hz'.symm)⟩
    · rintro ⟨z, rfl, _⟩
      have hfirst := (h₁ T ((z ≫ j₂) ≫ j₁)).mpr
        ⟨z ≫ j₂, rfl, fun w hw => (cancel_mono j₁).mp hw⟩
      have hrest := (h₂ T (z ≫ j₂)).mpr
        ⟨z, rfl, fun w hw => (cancel_mono j₂).mp hw⟩
      change Endomorphisms.Core.SatisfiesEquations R (φ.app (.op T) ((z ≫ j₂) ≫ j₁)) at hrest
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · simpa only [Category.assoc] using hfirst
      · simpa only [Category.assoc] using hrest s hs

theorem finite_proper_equations_closed_locus
    (R : List (Endomorphisms.Core.FamilyMorphismEquation F))
    {M : Over S} [IsLocallyNoetherian M.left] (φ : yoneda.obj M ⟶ F) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ M), Endomorphisms.Core.SatisfiesEquations R (φ.app (.op T) x) ↔
        ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅ ((Endomorphisms.Core.solutionSubfunctor R).preimage φ).toFunctor,
        e.hom ≫ ((Endomorphisms.Core.solutionSubfunctor R).preimage φ).ι = yoneda.map j := by
  obtain ⟨Z, j, hj, htest⟩ := finite_proper_equations_closed_lifts R φ
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  refine ⟨Z, j, hj, htest, ?_⟩
  apply SubfunctorRepresentations.subfunctor_representation_of_lifts
  intro T x
  constructor
  · intro hx
    exact ((htest T x).mp hx).exists
  · rintro ⟨y, hy⟩
    exact (htest T x).mpr ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProperEquationLoci.Core
