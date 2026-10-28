import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

/-! # Prime Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder

noncomputable section

/-! Prime-quotient orders in a surface stalk are the native geometric
orders on the actual reduced closures of its height-one primes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

variable (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] (x : X)
  (p : PrimeSpectrum (X.presheaf.stalk x))

omit [IsIntegral X] [IsLocallyNoetherian X] in
theorem image_ne_zero (r : X.presheaf.stalk x) (hr : r ∉ p.asIdeal) :
    Local.Principal.supportStalkMap X (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p) r ≠ 0 := by
  intro hz
  apply hr
  have hk := PrimeQuotient.kernel_eq X (DivisorSupport.primeClosure X x p) x
    (DivisorSupport.point_mem_primeClosure X x p) p (DivisorSupport.primeClosure_point X x p).symm
  rw [← hk]
  exact RingHom.mem_ker.mpr hz

omit [IsIntegral X] [IsLocallyNoetherian X] in
theorem quotient_order (r : X.presheaf.stalk x) :
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme (DivisorSupport.primeClosure X x p)).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p)))
      (Local.Principal.supportStalkMap X (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p) r) =
      Ring.ord ((X.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r) := by
  let σ := Local.Principal.supportStalkMap X (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p)
  have hk : RingHom.ker σ.hom = p.asIdeal := PrimeQuotient.kernel_eq X
    (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p) p (DivisorSupport.primeClosure_point X x p).symm
  rw [← hk]
  exact OrderQuotientTransport.ord σ.hom
    (Local.Principal.supportStalkMap_surjective X (DivisorSupport.primeClosure X x p) x (DivisorSupport.point_mem_primeClosure X x p)) r

theorem geometric_order (hx : Order.coheight x = 2) (hp : p.asIdeal.height = 1)
    (r : X.presheaf.stalk x) (hr : r ∉ p.asIdeal) :
    let W := DivisorSupport.primeClosure X x p
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x (DivisorSupport.point_mem_primeClosure X x p)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
        (Local.Principal.supportStalkMap X W x (DivisorSupport.point_mem_primeClosure X x p) r)) y =
      ((Ring.ord ((X.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℤ) := by
  have hW : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (DivisorSupport.primeClosure X x p)) = 1 := by
    rw [DivisorSupport.primeClosure_point, ← Localization.height_eq_coheight_image]
    exact hp
  have hy := AdjacentSupportCoheight.coheight_one X (DivisorSupport.primeClosure X x p) hW x hx
    (DivisorSupport.point_mem_primeClosure X x p)
  apply (Affine.PrincipalOrder.stalk_order _ _ hy _ (image_ne_zero X x p r hr)).trans
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (quotient_order X x p r)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder
