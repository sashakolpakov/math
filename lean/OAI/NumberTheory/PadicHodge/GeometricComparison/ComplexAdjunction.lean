import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Complex Adjunction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAdjunction.ComplexAdjunctionComponents

noncomputable section

/-! The actual adjunction on complexes has the original adjunction on each coefficient. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι : Type*} (c : ComplexShape ι)

theorem homEquiv_f (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (a : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι) :
    ((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj c).homEquiv K L a).f i =
      adj.homEquiv (K.X i) (L.X i) (a.f i) :=
  (congrArg (fun k => k.f i) ((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj c).homEquiv_unit K L a)).trans
    (adj.homEquiv_unit _ _ (a.f i)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAdjunction.ComplexAdjunctionComponents
