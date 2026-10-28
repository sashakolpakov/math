import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportSpectrum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Normal
import Mathlib.RingTheory.Ideal.Height

/-! # Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk

noncomputable section

/-! The native ambient stalk at a codimension-two intersection of divisors
has dimension two. Positive-codimension reduced support stalks are torsion
modules over the ambient domain, as witnessed by their actual defining ideal. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]

include m

theorem coheight_two (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hCA : C.val ≤ A.val) : coheight (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) = 2 := by
  apply le_antisymm
  · simpa only [C.property, Nat.cast_ofNat] using CurveSupports.coheight_le_codimension X m C.val
  · have hne : C.val ≠ A.val := by
      intro h
      have he := congrArg X.supportCodimension h
      rw [C.property, A.property] at he
      omega
    have hA : coheight A.val = 1 := by
      simpa only [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso] using CurveSupports.coheight_one X m A
    rw [CycleClass.Thom.IntersectionGeometry.supportPoint, coheight_orderIso]
    simpa only [hA, one_add_one_eq_two] using coheight_add_one_le (lt_of_le_of_ne hCA hne)

theorem maximalIdeal_height_two (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hCA : C.val ≤ A.val) :
    (IsLocalRing.maximalIdeal (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))).height = 2 := by
  apply WithBot.coe_injective
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight,
    coheight_two X m A C hCA]

theorem supportStalkMap_ker_ne_bot (p : ℕ) (hp : 0 < p) (A : X.DimensionCycleSupport p)
    (x : X.carrier) (hx : x ∈ (A.val : Set X.carrier)) :
    RingHom.ker (Local.Principal.supportStalkMap X.carrier A.val x hx).hom ≠ ⊥ := by
  let D := ZeroComponents.containingComponent X m A.val
  let z := CycleClass.Thom.IntersectionGeometry.supportPoint D.val
  have hxD : x ∈ (D.val : Set X.carrier) :=
    ZeroComponents.subset_containingComponent X m A.val hx
  have hzx : z ⤳ x :=
    (D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).specializes hxD
  have hzrange : z ∈ Set.range (X.carrier.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hzx
  obtain ⟨q, hq⟩ := hzrange
  intro hker
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val x hx)
  let σ := Local.Principal.supportStalkMap X.carrier A.val x hx
  let : Algebra R T := σ.hom.toAlgebra
  have hσ : Function.Bijective σ.hom :=
    ⟨(RingHom.injective_iff_ker_eq_bot σ.hom).mpr hker,
      Local.Principal.supportStalkMap_surjective X.carrier A.val x hx⟩
  let e : R ≃ₐ[R] T := AlgEquiv.ofBijective (Algebra.ofId R T) hσ
  have hsupport : Module.support R T = Set.univ := by
    rw [← e.toLinearEquiv.support_eq]
    exact Module.support_of_isTorsionFree
  have hzA : z ∈ (A.val : Set X.carrier) := by
    rw [← hq]
    apply Local.SupportSpectrum.image_mem_support X.carrier A.val x hx q
    change q ∈ Module.support R T
    rw [hsupport]
    trivial
  have hDA : D.val ≤ A.val := by
    change (D.val : Set X.carrier) ⊆ (A.val : Set X.carrier)
    exact (Supports.supportPoint_mem_iff_subset
      (⟨(A.val : Set X.carrier), A.val.isClosed⟩ : Closeds X.carrier) D.val).mp hzA
  have hdim := (Supports.codimension_strictAnti X m).antitone hDA
  rw [D.property, A.property] at hdim
  omega

theorem localSupport_torsion (p : ℕ) (hp : 0 < p) (A : X.DimensionCycleSupport p)
    (x : X.carrier) (hx : x ∈ (A.val : Set X.carrier)) :
    ∀ a : CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val x hx,
      ∃ r : X.carrier.presheaf.stalk x, r ≠ 0 ∧ r • a = 0 := by
  have hker := supportStalkMap_ker_ne_bot X m p hp A x hx
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro a
  change (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val x hx) at a
  refine ⟨r, hr0, ?_⟩
  change Local.Principal.supportStalkMap X.carrier A.val x hx r * a = 0
  rw [RingHom.mem_ker.mp hr, zero_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Stalk
