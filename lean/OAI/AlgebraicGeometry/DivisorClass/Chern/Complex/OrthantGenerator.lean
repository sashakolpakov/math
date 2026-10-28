import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantCircleNormalization
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology

/-! # Orthant Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.OrthantGenerator

noncomputable section

/-!
# ChernClass: the specified complex local generator has the explicit sphere boundary

The local-to-sphere isomorphism is the original relative boundary followed
by radial projection and ordered real coordinates. Its inverse applied to
the explicit signed-orthant cycle is exactly the original positive local
generator. No new local orientation or alternative generator is introduced.
-/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def positiveComplexOrthantLocalClass (p : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) :=
  (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1)
    (Nat.succ_ne_zero (2 * p))).inv (OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1))

theorem positiveComplexOrthantLocalClass_coordinate (p : ℕ) :
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).hom (positiveComplexOrthantLocalClass p) = 1 := by
  change (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereTopHomologyIso (2 * p)).hom
    ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1) _).hom
      ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1) _).inv
        (OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1)))) = 1
  rw [Iso.inv_hom_id_apply]
  exact OrthantCircleNormalization.orientedComplexBoundarySphere_coordinate p

theorem positiveComplexOrthantLocalClass_eq_originalGenerator (p : ℕ) :
    positiveComplexOrthantLocalClass p = (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).inv 1 := by
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).toLinearEquiv.injective
  change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).hom _ =
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).hom _
  rw [positiveComplexOrthantLocalClass_coordinate, Iso.inv_hom_id_apply]

/-- The native geometric generator, under its actual boundary and coordinate
maps, gives the explicit positively oriented odd-dimensional sphere. -/
theorem positiveComplexOriginalGenerator_sphereBoundary (p : ℕ) :
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1)
        (Nat.succ_ne_zero (2 * p))).hom
      ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalTopLocalHomologyIso p).inv 1) =
      OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1) := by
  rw [← positiveComplexOrthantLocalClass_eq_originalGenerator]
  exact (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.positiveComplexNormalLocalStandardSphereIso p (2 * p + 1)
    (Nat.succ_ne_zero (2 * p))).inv_hom_id_apply _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.OrthantGenerator
