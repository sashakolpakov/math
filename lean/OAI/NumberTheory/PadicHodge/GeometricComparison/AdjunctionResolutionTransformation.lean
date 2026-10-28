import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Adjunction Resolution Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionTransformation.AdjunctionResolutionPullback

noncomputable section

/-! An actual direct-image comparison of resolution functors has a natural inverse-image mate. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  (T : C ⥤ CochainComplex C ℕ) (N : D ⥤ CochainComplex D ℕ)
  (e : G ⋙ T ≅ N ⋙ G.mapHomologicalComplex (.up ℕ))

def directMap (P : C) : T.obj P ⟶ (G.mapHomologicalComplex (.up ℕ)).obj (N.obj (F.obj P)) :=
  T.map (adj.unit.app P) ≫ e.hom.app (F.obj P)

omit [F.Additive] in
theorem direct_naturality {P Q : C} (a : P ⟶ Q) :
    T.map a ≫ directMap adj T N e Q =
      directMap adj T N e P ≫ (G.mapHomologicalComplex (.up ℕ)).map (N.map (F.map a)) := by
  have h₁ : T.map a ≫ T.map (adj.unit.app Q) =
      T.map (adj.unit.app P) ≫ T.map (G.map (F.map a)) :=
    (T.map_comp _ _).symm.trans ((congrArg T.map (adj.unit.naturality a)).trans (T.map_comp _ _))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ (e.hom.naturality (F.map a))

def map (P : C) : (F.mapHomologicalComplex (.up ℕ)).obj (T.obj P) ⟶ N.obj (F.obj P) :=
  ((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)).homEquiv _ _).symm (directMap adj T N e P)

theorem naturality {P Q : C} (a : P ⟶ Q) :
    (F.mapHomologicalComplex (.up ℕ)).map (T.map a) ≫ AdjunctionResolutionPullback.map adj T N e Q =
      AdjunctionResolutionPullback.map adj T N e P ≫ N.map (F.map a) :=
  (AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj (.up ℕ)).homEquiv_naturality_right_square _ _ _ _
    (direct_naturality adj T N e a)

def transformation : T ⋙ F.mapHomologicalComplex (.up ℕ) ⟶ F ⋙ N where
  app P := AdjunctionResolutionPullback.map adj T N e P
  naturality _ _ a := AdjunctionResolutionPullback.naturality adj T N e a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdjunctionResolutionTransformation.AdjunctionResolutionPullback
