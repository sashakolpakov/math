import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder

/-! # Geometric Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.GeometricOrder

noncomputable section

/-! A nonclosed prime of an ambient stalk with one-dimensional
quotient determines a codimension-one point on its actual reduced
closure. Its principal parameter order is the geometric divisor order. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

variable (X : Scheme) [IsLocallyNoetherian X] (x : X)
  (p : PrimeSpectrum (X.presheaf.stalk x))

omit [IsLocallyNoetherian X] in
theorem coheight_one (hp : p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x))
    (hd : ringKrullDim ((X.presheaf.stalk x) ⧸ p.asIdeal) ≤ 1) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage (Stalk.DivisorSupport.primeClosure X x p) x (Stalk.DivisorSupport.point_mem_primeClosure X x p)) = 1 := by
  let W := Stalk.DivisorSupport.primeClosure X x p
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x (Stalk.DivisorSupport.point_mem_primeClosure X x p)
  let R := X.presheaf.stalk x
  let T := Y.presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X W x (Stalk.DivisorSupport.point_mem_primeClosure X x p)
  let : Algebra R T := σ.hom.toAlgebra
  have hσ : Function.Surjective (Algebra.ofId R T) :=
    Local.Principal.supportStalkMap_surjective X W x (Stalk.DivisorSupport.point_mem_primeClosure X x p)
  have hk : RingHom.ker σ.hom = p.asIdeal := Stalk.PrimeQuotient.kernel_eq X W x
    (Stalk.DivisorSupport.point_mem_primeClosure X x p) p (Stalk.DivisorSupport.primeClosure_point X x p).symm
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T := by
    rw [← hk]
    exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  rw [he, ringKrullDim_stalk_eq_coheight] at hd
  have hle : coheight y ≤ 1 := WithBot.coe_le_coe.mp hd
  have hy : y ≠ genericPoint Y := by
    intro hy
    apply hp
    apply (X.fromSpecStalk x).isEmbedding.injective
    rw [Scheme.fromSpecStalk_closedPoint, ← Stalk.DivisorSupport.primeClosure_point X x p]
    exact (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).symm.trans
      ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W) hy.symm).trans
        (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x (Stalk.DivisorSupport.point_mem_primeClosure X x p)))
  have hspec : y ≤ genericPoint Y := genericPoint_specializes y
  have hlt : y < genericPoint Y := lt_of_le_not_ge hspec (by
    intro h
    exact hy (Specializes.antisymm h hspec).eq)
  have htop : coheight (genericPoint Y) = 0 := (isTop_top : IsTop (⊤ : Y)).isMax.coheight_eq_zero
  have hlo := coheight_add_one_le hlt
  rw [htop, zero_add] at hlo
  exact le_antisymm hle hlo

theorem order (hp : p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x))
    (hd : ringKrullDim ((X.presheaf.stalk x) ⧸ p.asIdeal) ≤ 1)
    (r : X.presheaf.stalk x) (hr : r ∉ p.asIdeal) :
    let W := Stalk.DivisorSupport.primeClosure X x p
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x (Stalk.DivisorSupport.point_mem_primeClosure X x p)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField
        (Local.Principal.supportStalkMap X W x (Stalk.DivisorSupport.point_mem_primeClosure X x p) r)) y =
      ((Ring.ord ((X.presheaf.stalk x) ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℤ) := by
  apply (Affine.PrincipalOrder.stalk_order _ _ (coheight_one X x p hp hd) _
    (Stalk.PrimeOrder.image_ne_zero X x p r hr)).trans
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Stalk.PrimeOrder.quotient_order X x p r)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.GeometricOrder
