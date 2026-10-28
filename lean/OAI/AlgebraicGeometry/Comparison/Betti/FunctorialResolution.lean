import OAI.AlgebraicGeometry.Comparison.Betti.FunctorialCokernel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Whiskering

/-! # Functorial Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FunctorialResolution

noncomputable section

/-! Iterating the actual cokernel gives a functorial cochain resolution.
Its exactness follows from the canonical short exact sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (T : C ⥤ C) (η : 𝟭 C ⟶ T)

def residualFunctor : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => residualFunctor n ⋙ FunctorialCokernel.Resolution.quotientFunctor T η

instance residualFunctor_additive [T.Additive] (n : ℕ) :
    (FunctorialResolution.residualFunctor T η n).Additive := by
  induction n with
  | zero => exact inferInstanceAs (Functor.Additive (𝟭 C))
  | succ n ih =>
    exact inferInstanceAs ((FunctorialResolution.residualFunctor T η n ⋙ FunctorialCokernel.Resolution.quotientFunctor T η).Additive)

def resolutionTerm (n : ℕ) : C ⥤ C := FunctorialResolution.residualFunctor T η n ⋙ T

instance resolutionTerm_additive [T.Additive] (n : ℕ) :
    (resolutionTerm T η n).Additive :=
  inferInstanceAs ((FunctorialResolution.residualFunctor T η n ⋙ T).Additive)

def resolutionDifferential (n : ℕ) : resolutionTerm T η n ⟶ resolutionTerm T η (n + 1) :=
  Functor.whiskerLeft (FunctorialResolution.residualFunctor T η n) (FunctorialCokernel.Resolution.quotientProjection T η) ≫
    Functor.whiskerLeft (FunctorialResolution.residualFunctor T η (n + 1)) η

theorem resolutionDifferential_squared (X : C) (n : ℕ) :
    (resolutionDifferential T η n).app X ≫ (resolutionDifferential T η (n + 1)).app X = 0 := by
  let A := (FunctorialResolution.residualFunctor T η n).obj X
  change (cokernel.π (η.app A) ≫ η.app (cokernel (η.app A))) ≫
    (cokernel.π (η.app (cokernel (η.app A))) ≫
      η.app (cokernel (η.app (cokernel (η.app A))))) = 0
  simp only [Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]

def resolutionComplex (X : C) : CochainComplex C ℕ :=
  CochainComplex.of (fun n => (resolutionTerm T η n).obj X)
    (fun n => (resolutionDifferential T η n).app X) (resolutionDifferential_squared T η X)

theorem resolutionComplex_d (X : C) (n : ℕ) :
    (resolutionComplex T η X).d n (n + 1) = (resolutionDifferential T η n).app X :=
  CochainComplex.of_d (fun k => (resolutionTerm T η k).obj X)
    (fun k => (resolutionDifferential T η k).app X) n

def resolutionMap {X Y : C} (f : X ⟶ Y) : resolutionComplex T η X ⟶ resolutionComplex T η Y :=
  CochainComplex.ofHom (fun n => (resolutionTerm T η n).map f) (fun n => by
    rw [resolutionComplex_d, resolutionComplex_d]
    exact (resolutionDifferential T η n).naturality f)

def resolutionFunctor : C ⥤ CochainComplex C ℕ where
  obj := resolutionComplex T η
  map := resolutionMap T η
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (resolutionTerm T η n).map_id X
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (resolutionTerm T η n).map_comp f g

instance resolutionFunctor_additive [T.Additive] : (resolutionFunctor T η).Additive where
  map_add {X Y} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (resolutionTerm T η n).map_add

theorem exact_precompose_epi (S : ShortComplex C) (hS : S.Exact)
    {W : C} (p : W ⟶ S.X₁) [Epi p] :
    (ShortComplex.mk (p ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero])).Exact := by
  let φ : ShortComplex.mk (p ≫ S.f) S.g (by rw [Category.assoc, S.zero, comp_zero]) ⟶ S :=
    { τ₁ := p, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  have : Epi φ.τ₁ := inferInstanceAs (Epi p)
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 S.X₃))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS

theorem exact_postcompose_mono (S : ShortComplex C) (hS : S.Exact)
    {W : C} (i : S.X₃ ⟶ W) [Mono i] :
    (ShortComplex.mk S.f (S.g ≫ i) (by rw [← Category.assoc, S.zero, zero_comp])).Exact := by
  let φ : S ⟶ ShortComplex.mk S.f (S.g ≫ i) (by rw [← Category.assoc, S.zero, zero_comp]) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := i }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 S.X₁))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono i)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hS

variable (hη : ∀ X, Mono (η.app X))

theorem resolution_augmentation_comp (X : C) :
    η.app X ≫ (resolutionComplex T η X).d 0 1 = 0 := by
  rw [resolutionComplex_d]
  change η.app X ≫ (cokernel.π (η.app X) ≫ η.app (cokernel (η.app X))) = 0
  rw [← Category.assoc, cokernel.condition, zero_comp]

include hη

theorem resolution_augmentation_exact (X : C) :
    (ShortComplex.mk (η.app X) ((resolutionComplex T η X).d 0 1)
      (resolution_augmentation_comp T η X)).Exact := by
  have := hη X
  have := hη (cokernel (η.app X))
  let S := ShortComplex.mk (η.app X) (cokernel.π (η.app X)) (cokernel.condition (η.app X))
  have hS : S.Exact := (FunctorialCokernel.Resolution.quotientShortComplex_shortExact T η X).exact
  have h := exact_postcompose_mono S hS (η.app (cokernel (η.app X)))
  simp only [resolutionComplex_d]
  convert h using 1
  rfl

theorem resolutionComplex_exactAt_succ (X : C) (n : ℕ) :
    (resolutionComplex T η X).ExactAt (n + 1) := by
  let A := (FunctorialResolution.residualFunctor T η n).obj X
  let B := cokernel (η.app A)
  have := hη B
  have := hη (cokernel (η.app B))
  let S := ShortComplex.mk (η.app B) (cokernel.π (η.app B)) (cokernel.condition (η.app B))
  have hS : S.Exact := (FunctorialCokernel.Resolution.quotientShortComplex_shortExact T η B).exact
  have h := exact_precompose_epi S hS (cokernel.π (η.app A))
  have h' := exact_postcompose_mono _ h (η.app (cokernel (η.app B)))
  apply ((resolutionComplex T η X).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mpr
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', resolutionComplex_d]
  convert h' using 1
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.FunctorialResolution
