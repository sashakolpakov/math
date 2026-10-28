import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneEquivalence

/-! # One Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneTransport.FirstThreeHOneTransport

noncomputable section

/-! A cochain map invertible in its first three terms preserves degree-one derived sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

def derived : CochainComplex C ℕ ⥤ DerivedCategory C :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙ DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ)

def map (A : C) {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    ((DerivedCategory.singleFunctor C 0).obj A ⟶ (derived.obj K)) →
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (derived.obj L)) :=
  fun x => x ≫ derived.map f

omit [HasDerivedCategory.{w} C] in
theorem firstThree_isIso {K L : CochainComplex C ℕ} (f : K ⟶ L)
    (h : ∀ n : ℕ, n ≤ 2 → IsIso (f.f n)) : IsIso (ThreeComplex.FirstThreeComplex.map f) := by
  have (n : ℕ) : IsIso ((ThreeComplex.FirstThreeComplex.map f).f n) := by
    rcases n with _ | (_ | (_ | n))
    · exact h 0 (by omega)
    · exact h 1 (by omega)
    · exact h 2 (by omega)
    · exact (isZero_zero C).isIso (isZero_zero C) _
  exact HomologicalComplex.Hom.isIso_of_components _

theorem postcompose_bijective {D : Type*} [Category* D] {X Y Z : D} (g : Y ⟶ Z) [IsIso g] :
    Function.Bijective (fun x : X ⟶ Y => x ≫ g) := by
  constructor
  · intro x y h
    exact (cancel_mono g).mp h
  · intro z
    refine ⟨z ≫ inv g, ?_⟩
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem map_naturality (A : C) {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    map A (ThreeComplex.FirstThreeComplex.projection L) ∘ map A f =
      map A (ThreeComplex.FirstThreeComplex.map f) ∘ map A (ThreeComplex.FirstThreeComplex.projection K) := by
  funext x
  change (x ≫ derived.map f) ≫ derived.map (ThreeComplex.FirstThreeComplex.projection L) =
    (x ≫ derived.map (ThreeComplex.FirstThreeComplex.projection K)) ≫ derived.map (ThreeComplex.FirstThreeComplex.map f)
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ThreeComplex.FirstThreeComplex.projection_naturality]

theorem bijective (A : C) {K L : CochainComplex C ℕ} (f : K ⟶ L)
    (h : ∀ n : ℕ, n ≤ 2 → IsIso (f.f n)) : Function.Bijective (map A f) := by
  let : IsIso (ThreeComplex.FirstThreeComplex.map f) := firstThree_isIso f h
  let : IsIso (derived.map (ThreeComplex.FirstThreeComplex.map f)) := derived.map_isIso _
  have hK : Function.Bijective (map A (ThreeComplex.FirstThreeComplex.projection K)) :=
    OneEquivalence.FirstThreeComplex.hone_bijective K A
  have hL : Function.Bijective (map A (ThreeComplex.FirstThreeComplex.projection L)) :=
    OneEquivalence.FirstThreeComplex.hone_bijective L A
  have hF : Function.Bijective (map A (ThreeComplex.FirstThreeComplex.map f)) := postcompose_bijective _
  apply (Function.Bijective.of_comp_iff' hL (map A f)).mp
  rw [map_naturality]
  exact hF.comp hK

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.OneTransport.FirstThreeHOneTransport
