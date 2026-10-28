import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntermediateSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight

/-! # Nested Support Coheight -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportCoheight

noncomputable section

/-! Inside any reduced support in a smooth projective ambient scheme,
point codimension is the difference of the two ambient codimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m in
theorem between (r d p : ℕ) (W : X.DimensionCycleSupport r) (C : X.DimensionCycleSupport p)
    (h : r + d ≤ p) (hCW : C.val ≤ W.val) :
    ∃ A : X.DimensionCycleSupport (r + d), C.val ≤ A.val ∧ A.val ≤ W.val := by
  induction d with
  | zero => exact ⟨W, hCW, le_rfl⟩
  | succ d ih =>
    obtain ⟨V, hCV, hVW⟩ := ih (by omega)
    obtain ⟨A, hCA, hAV⟩ := IntermediateSupports.next_support X m (r + d) p V C (by omega) hCV
    exact ⟨A, hCA, hAV.trans hVW⟩

include m in
theorem upper (r d : ℕ) (W : X.DimensionCycleSupport r) (C : X.DimensionCycleSupport (r + d))
    (hCW : C.val ≤ W.val) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
      (hCW (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem)) ≤ d := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  have hxW : x ∈ (W.val : Set X.carrier) := hCW (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW
  let R := X.carrier.presheaf.stalk x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y
  let σ := Local.Principal.supportStalkMap X.carrier W.val x hxW
  let : Algebra R T := σ.hom.toAlgebra
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier W.val x hxW
  have hp : p.asIdeal.height = r := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact IntermediateSupports.support_coheight X m r W
  have hdim : ringKrullDim R = (r + d : ℕ) := by
    rw [ringKrullDim_stalk_eq_coheight, IntermediateSupports.support_coheight X m (r + d) C]
    rfl
  have hq := Affine.DivisorDimension.quotient_dimension_add_height_le R p
  have hσ : Function.Surjective (Algebra.ofId R T) := Local.Principal.supportStalkMap_surjective X.carrier W.val x hxW
  have he : ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim T :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R T) hσ).toRingEquiv.ringKrullDim
  rw [hp, he, ringKrullDim_stalk_eq_coheight, hdim] at hq
  have hy : (coheight y : WithBot ℕ∞) ≤ (d : ℕ) := by
    apply (ENat.WithBot.add_le_add_natCast_left_iff (c := r)).mp
    norm_cast at hq ⊢
  exact WithBot.coe_le_coe.mp hy

include m in
theorem eq (r d : ℕ) (W : X.DimensionCycleSupport r) (C : X.DimensionCycleSupport (r + d))
    (hCW : C.val ≤ W.val) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
      (hCW (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem)) = d := by
  apply le_antisymm (upper X m r d W C hCW)
  induction d with
  | zero => exact zero_le
  | succ d ih =>
    obtain ⟨A, hCA, hAW⟩ := between X m r d (r + (d + 1)) W C (by omega) hCW
    let yC := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
      (hCW (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem)
    let yA := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
      (hAW (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem)
    have hle : yC ≤ yA := by
      apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.isInducing.specializes_iff.mp
      rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
      exact (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).specializes
        (hCA (C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem)
    have hne : yC ≠ yA := by
      intro he
      have hp := congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W.val) he
      rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec] at hp
      have hgrade := congrArg X.supportCodimension (irreducibleSetEquivPoints.injective hp)
      rw [C.property, A.property] at hgrade
      omega
    have hlt : yC < yA := lt_of_le_not_ge hle (fun h => hne (Specializes.antisymm h hle).eq)
    have h := coheight_add_one_le hlt
    have hA := ih A hAW
    have hA' : ((d + 1 : ℕ) : ℕ∞) ≤ coheight yA + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add hA (le_refl (1 : ℕ∞))
    exact hA'.trans h

include m in
theorem difference (W C : IrreducibleCloseds X.carrier) (hCW : C ≤ W) :
    coheight (CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C)
      (hCW (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem)) =
        (X.supportCodimension C - X.supportCodimension W : ℕ) := by
  have hle := (Supports.codimension_strictAnti X m).antitone hCW
  exact NestedSupportCoheight.eq X m (X.supportCodimension W) (X.supportCodimension C - X.supportCodimension W)
    ⟨W, rfl⟩ ⟨C, by omega⟩ hCW

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportCoheight
