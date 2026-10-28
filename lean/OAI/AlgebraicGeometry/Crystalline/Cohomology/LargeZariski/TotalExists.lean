import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TotalComplexUpNat

/-! # Total Exists -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.TotalExists.LargeZariskiTotalExists

noncomputable section

/-! # Explicit existence of the native first-quadrant total complexes -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

instance total (K : HomologicalComplex₂
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R))
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)) : K.HasTotal (ComplexShape.up ℕ) := by
  intro n
  have h := (Colimits.LargeZariskiColimits.sheaves R X).has_colimits_of_shape
    (Discrete {i : ℕ × ℕ // ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) i = n})
  exact h.has_colimit
    (Discrete.functor (K.toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) n))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.TotalExists.LargeZariskiTotalExists
