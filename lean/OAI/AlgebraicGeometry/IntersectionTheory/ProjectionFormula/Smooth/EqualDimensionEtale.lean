import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDifferentials
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.OverScalars

/-! # Equal Dimension Etale -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.EqualDimensionEtale

noncomputable section

/-! An unramified map between smooth schemes of the same dimension
over a field is formally etale at that stalk, by the Jacobi-Zariski sequence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem stalk {K : Type u} [Field K] {X Y : Scheme.{u}}
    (i : X ⟶ Y) (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (hi : i ≫ g = f) (m : ℕ)
    [SmoothOfRelativeDimension m f] [SmoothOfRelativeDimension m g] (x : X)
    (hu : (i.stalkMap x).hom.FormallyUnramified) : (i.stalkMap x).hom.FormallyEtale := by
  let A := Y.presheaf.stalk (i x)
  let B := X.presheaf.stalk x
  let := Stalk.PointAlgebra.scalarAlgebra g (i x)
  let := Stalk.PointAlgebra.scalarAlgebra f x
  let φ := Stalk.OverScalars.map i f g hi x
  have hφ : φ.toRingHom = (i.stalkMap x).hom := Stalk.OverScalars.ringHom i f g hi x
  let := φ.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  obtain ⟨hAS, hAF, hAfin, hAdim⟩ := StalkDifferentials.data g m (i x)
  obtain ⟨hBS, hBF, hBfin, hBdim⟩ := StalkDifferentials.data f m x
  let := hAS
  let := hAF
  let := hAfin
  let := hBS
  let := hBF
  let := hBfin
  let : Algebra.FormallyUnramified A B := by
    change φ.toRingHom.FormallyUnramified
    rw [hφ]
    exact hu
  rw [← hφ]
  apply Etale.FromDifferentials.of_finrank_eq K A B
  rw [Module.finrank_baseChange, hAdim, hBdim]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.EqualDimensionEtale
