import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeMaps

/-! # Cube Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeComposition

noncomputable section

/-! Cubical sum maps evaluated on arbitrary test-scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem nativeCubeProjection_comp (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y z : T ⟶ A.toOver) (k : Fin 3) :
    lift (lift x y) z ≫ CubeMaps.nativeCubeProjection A k = ![x, y, z] k := by
  fin_cases k
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ fst A.toOver A.toOver) (lift_fst (lift x y) z)).trans (lift_fst x y))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ snd A.toOver A.toOver) (lift_fst (lift x y) z)).trans (lift_snd x y))
  · exact lift_snd (lift x y) z

theorem nativeCubePositiveMap_comp (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y z : T ⟶ A.toOver) (k : Fin 4) :
    lift (lift x y) z ≫ CubeMaps.nativeCubePositiveMap A k = ![x * y * z, x, y, z] k := by
  have h0 := nativeCubeProjection_comp A x y z 0
  have h1 := nativeCubeProjection_comp A x y z 1
  have h2 := nativeCubeProjection_comp A x y z 2
  fin_cases k
  · exact (MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b)
      ((MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b) h0 h1)) h2)
  · exact h0
  · exact h1
  · exact h2

theorem nativeCubeNegativeMap_comp (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y z : T ⟶ A.toOver) (k : Fin 3) :
    lift (lift x y) z ≫ CubeMaps.nativeCubeNegativeMap A k = ![x * y, x * z, y * z] k := by
  have h0 := nativeCubeProjection_comp A x y z 0
  have h1 := nativeCubeProjection_comp A x y z 1
  have h2 := nativeCubeProjection_comp A x y z 2
  fin_cases k
  · exact (MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b) h0 h1)
  · exact (MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b) h0 h2)
  · exact (MonObj.comp_mul _ _ _).trans (congrArg₂ (fun a b => a * b) h1 h2)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeComposition
