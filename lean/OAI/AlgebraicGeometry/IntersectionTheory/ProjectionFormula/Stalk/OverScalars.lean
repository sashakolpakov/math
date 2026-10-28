import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps

/-! # Over Scalars -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.OverScalars

noncomputable section

/-! Stalk maps as algebra homomorphisms for specified, commuting
structure maps to the coefficient field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

def map (i : X ⟶ Y) (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (h : i ≫ g = f) (x : X) :
    letI := PointAlgebra.scalarAlgebra g (i x)
    letI := PointAlgebra.scalarAlgebra f x
    Y.presheaf.stalk (i x) →ₐ[K] X.presheaf.stalk x := by
  let := PointAlgebra.scalarAlgebra g (i x)
  let := PointAlgebra.scalarAlgebra f x
  refine { (i.stalkMap x).hom with commutes' := ?_ }
  intro c
  subst f
  exact (ScalarMaps.stalk i g x).commutes c

theorem ringHom (i : X ⟶ Y) (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (h : i ≫ g = f) (x : X) :
    letI := PointAlgebra.scalarAlgebra g (i x)
    letI := PointAlgebra.scalarAlgebra f x
    (map i f g h x).toRingHom = (i.stalkMap x).hom := rfl

theorem apply (i : X ⟶ Y) (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (h : i ≫ g = f) (x : X) (r : Y.presheaf.stalk (i x)) :
    map i f g h x r = i.stalkMap x r := by
  exact RingHom.congr_fun (ringHom i f g h x) r

instance isLocal (i : X ⟶ Y) (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    (h : i ≫ g = f) (x : X) :
    letI := PointAlgebra.scalarAlgebra g (i x)
    letI := PointAlgebra.scalarAlgebra f x
    IsLocalHom (map i f g h x).toRingHom := by
  let := PointAlgebra.scalarAlgebra g (i x)
  let := PointAlgebra.scalarAlgebra f x
  rw [ringHom]
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.OverScalars
