import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex
import Mathlib.Algebra.Homology.Additive

/-! # Map Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MapFunctor.FirstThreeMapFunctor

noncomputable section

/-! Taking the first three terms commutes with additive functors through the canonical zero-object isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)

def component : ∀ n,
    ((F.mapHomologicalComplex (.up ℕ)).obj (ThreeComplex.FirstThreeComplex.complex K)).X n ≅
      (ThreeComplex.FirstThreeComplex.complex ((F.mapHomologicalComplex (.up ℕ)).obj K)).X n
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | 2 => Iso.refl _
  | _ + 3 => (F.map_isZero (isZero_zero C)).isoZero

def iso : (F.mapHomologicalComplex (.up ℕ)).obj (ThreeComplex.FirstThreeComplex.complex K) ≅
    ThreeComplex.FirstThreeComplex.complex ((F.mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (component F K) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    rw [show ((F.mapHomologicalComplex (.up ℕ)).obj (ThreeComplex.FirstThreeComplex.complex K)).d n (n + 1) =
        F.map (ThreeComplex.FirstThreeComplex.differential K n) from
          congrArg F.map (CochainComplex.of_d _ _ n),
      show (ThreeComplex.FirstThreeComplex.complex ((F.mapHomologicalComplex (.up ℕ)).obj K)).d n (n + 1) =
        ThreeComplex.FirstThreeComplex.differential ((F.mapHomologicalComplex (.up ℕ)).obj K) n from
          CochainComplex.of_d _ _ n]
    rcases n with _ | (_ | n)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · change _ ≫ 0 = F.map 0 ≫ _
      rw [F.map_zero]
      erw [zero_comp, comp_zero])

theorem projection :
    (F.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.projection K) ≫ (iso F K).hom =
      ThreeComplex.FirstThreeComplex.projection ((F.mapHomologicalComplex (.up ℕ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · change F.map (𝟙 (K.X 0)) ≫ 𝟙 _ = 𝟙 _
    rw [F.map_id, Category.id_comp]
  · change F.map (𝟙 (K.X 1)) ≫ 𝟙 _ = 𝟙 _
    rw [F.map_id, Category.id_comp]
  · change F.map (𝟙 (K.X 2)) ≫ 𝟙 _ = 𝟙 _
    rw [F.map_id, Category.id_comp]
  · change F.map (0 : K.X (n + 3) ⟶ 0) ≫ (F.map_isZero (isZero_zero C)).isoZero.hom = 0
    rw [F.map_zero, zero_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MapFunctor.FirstThreeMapFunctor
