import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialMap
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Functorial Integer -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialInteger.FirstThreeFunctorialInteger

noncomputable section

/-! The original first-three projection square remains a commuting square
after extension to integer-indexed complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def map : (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ⟶
    L.extend ComplexShape.embeddingUpNat :=
  (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat K).hom ≫
    HomologicalComplex.extendMap f ComplexShape.embeddingUpNat

def firstThreeMap :
    (F.mapHomologicalComplex (.up ℤ)).obj ((ThreeComplex.FirstThreeComplex.complex K).extend ComplexShape.embeddingUpNat) ⟶
      (ThreeComplex.FirstThreeComplex.complex L).extend ComplexShape.embeddingUpNat :=
  FirstThreeFunctorialInteger.map F (FunctorialMap.FirstThreeFunctorialMap.map F f)

theorem projection_square :
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap (ThreeComplex.FirstThreeComplex.projection K) ComplexShape.embeddingUpNat) ≫
      firstThreeMap F f = FirstThreeFunctorialInteger.map F f ≫
        HomologicalComplex.extendMap (ThreeComplex.FirstThreeComplex.projection L) ComplexShape.embeddingUpNat := by
  have h₁ := AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality F ComplexShape.embeddingUpNat
    (ThreeComplex.FirstThreeComplex.projection K)
  let T := ComplexShape.embeddingUpNat.extendFunctor D
  have h₂ := congrArg T.map (FunctorialMap.FirstThreeFunctorialMap.projection_square F f)
  rw [Functor.map_comp, Functor.map_comp] at h₂
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialInteger.FirstThreeFunctorialInteger
