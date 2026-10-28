import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.StalkImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

/-! # Image Stalk Module -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImageStalkModule

noncomputable section

/-! The native reduced-image support module of an integral closed
immersion is the actual source stalk with its native ambient action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

variable {X Y : Scheme} [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (y : Y)

omit [IsClosedImmersion i] in
theorem mem : i y ∈ (ImmersionSupport.support i : Set X) := subset_closure ⟨y, rfl⟩

omit [IsClosedImmersion i] in
theorem kernel : RingHom.ker (Local.Principal.supportStalkMap X (ImmersionSupport.support i) (i y) (mem i y)).hom =
    RingHom.ker (i.stalkMap y).hom := by
  let p := Integral.StalkImage.prime i y (i y) rfl
  have hp : X.fromSpecStalk (i y) p = CycleClass.Thom.IntersectionGeometry.supportPoint (ImmersionSupport.support i) :=
    (Integral.StalkImage.image i y (i y) rfl).trans (ImmersionSupport.support_point i).symm
  exact Stalk.PrimeQuotient.kernel_eq X (ImmersionSupport.support i) (i y) (mem i y) p hp

def moduleEquiv :
    letI : Algebra (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) := (i.stalkMap y).hom.toAlgebra
    CycleClass.Thom.IntersectionGeometry.localSupportModule X (ImmersionSupport.support i) (i y) (mem i y) ≃ₗ[X.presheaf.stalk (i y)] Y.presheaf.stalk y := by
  let R := X.presheaf.stalk (i y)
  let S := Y.presheaf.stalk y
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ImmersionSupport.support i)).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage (ImmersionSupport.support i) (i y) (mem i y))
  let : Algebra R S := (i.stalkMap y).hom.toAlgebra
  let : Algebra R T := (Local.Principal.supportStalkMap X (ImmersionSupport.support i) (i y) (mem i y)).hom.toAlgebra
  have hS : Function.Surjective (Algebra.ofId R S) := i.stalkMap_surjective y
  have hT : Function.Surjective (Algebra.ofId R T) :=
    Local.Principal.supportStalkMap_surjective X (ImmersionSupport.support i) (i y) (mem i y)
  exact (Ideal.quotientKerAlgEquivOfSurjective hT).symm.toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (kernel i y)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hS).toLinearEquiv)

def moduleEquiv_at (x : X) (h : i y = x) (hx : x ∈ (ImmersionSupport.support i : Set X)) :
    letI : Algebra (X.presheaf.stalk x) (Y.presheaf.stalk y) :=
      (Integral.StalkImage.map i y x h).hom.toAlgebra
    CycleClass.Thom.IntersectionGeometry.localSupportModule X (ImmersionSupport.support i) x hx ≃ₗ[X.presheaf.stalk x] Y.presheaf.stalk y := by
  subst x
  exact moduleEquiv i y

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImageStalkModule
