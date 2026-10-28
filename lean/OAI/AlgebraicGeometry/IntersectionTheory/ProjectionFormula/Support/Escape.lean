import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.CurveEscape
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder

/-! # Escape -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Escape

noncomputable section

/-! A support of codimension r+1 lies in an actual support of codimension r
on which any prescribed nonzero function at its generic point survives. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : X.DimensionCycleSupport (r + 1))
    (f : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (hf : f ≠ 0) :
    ∃ A : X.DimensionCycleSupport r, ∃ hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier),
      Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA f ≠ 0 := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  obtain ⟨p, hp, hfp⟩ := Local.CurveEscape.exists_prime R
    (by rw [IntermediateSupports.stalk_height X m (r + 1) C]; exact_mod_cast Nat.succ_pos r) f hf
  let W := Stalk.DivisorSupport.primeClosure X.carrier x p
  let hxW := Stalk.DivisorSupport.point_mem_primeClosure X.carrier x p
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X.carrier W x hxW
  let : Algebra R T := σ.hom.toAlgebra
  have hk : RingHom.ker σ.hom = p.asIdeal := Stalk.PrimeQuotient.kernel_eq
    X.carrier W x hxW p (Stalk.DivisorSupport.primeClosure_point X.carrier x p).symm
  have hσ : Function.Surjective (Algebra.ofId R T) := Local.Principal.supportStalkMap_surjective X.carrier W x hxW
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T := by
    rw [← hk]
    exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  have hy : Order.coheight y = 1 := by
    apply WithBot.coe_injective
    rw [← ringKrullDim_stalk_eq_coheight, ← he, hp]
    rfl
  let Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) := irreducibleSetEquivPoints.symm y
  have hZ : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = 1 := by
    change Order.coheight (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm y)) = 1
    rwa [irreducibleSetEquivPoints.apply_symm_apply]
  have himage : DivisorImage.image X W Z = C.val := by
    apply irreducibleSetEquivPoints.injective
    change CycleClass.Thom.IntersectionGeometry.supportPoint (DivisorImage.image X W Z) = CycleClass.Thom.IntersectionGeometry.supportPoint C.val
    rw [DivisorImage.image_point]
    change CycleClass.Geometric.GenericPoint.reducedSupportι W (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm y)) = x
    rw [irreducibleSetEquivPoints.apply_symm_apply, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
  have hW : X.supportCodimension W = r := by
    have h := DivisorImage.codimension X W m Z hZ
    rw [himage, C.property] at h
    omega
  exact ⟨⟨W, hW⟩, hxW, Stalk.PrimeOrder.image_ne_zero X.carrier x p f hfp⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Escape
