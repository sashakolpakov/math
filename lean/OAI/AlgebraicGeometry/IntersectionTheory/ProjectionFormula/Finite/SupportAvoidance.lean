import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Escape
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk

/-! # Support Avoidance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportAvoidance

noncomputable section

/-! A support lies in a support of one lower codimension which is contained
in none of a prescribed finite list of positive-codimension supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem exists_support (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (hq : 0 < q)
    (C : X.DimensionCycleSupport (r + 1)) (S : Finset (X.DimensionCycleSupport q)) :
    ∃ A : X.DimensionCycleSupport r, C.val ≤ A.val ∧ ∀ D ∈ S, ¬ A.val ≤ D.val := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := X.carrier.presheaf.stalk x
  let : IsDomain R := X.stalk_isDomain x
  let T := S.filter (fun D => x ∈ (D.val : Set X.carrier))
  have hT (D : T) : x ∈ (D.val.val : Set X.carrier) := (Finset.mem_filter.mp D.property).2
  have hker (D : T) := Divisor.Stalk.supportStalkMap_ker_ne_bot X m q hq D.val x (hT D)
  choose u hu hu0 using fun D : T => Submodule.exists_mem_ne_zero_of_ne_bot (hker D)
  let f : R := ∏ D : T, u D
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun D _ => hu0 D)
  obtain ⟨A, hxA, hfA⟩ := Support.Escape.exists_support X m r C f hf
  have hCA : C.val ≤ A.val := (Supports.supportPoint_mem_iff_subset
    (⟨(A.val : Set X.carrier), A.val.isClosed⟩ : Closeds X.carrier) C.val).mp hxA
  refine ⟨A, hCA, ?_⟩
  intro D hDS hAD
  have hxD : x ∈ (D.val : Set X.carrier) := hAD hxA
  have hDT : D ∈ T := Finset.mem_filter.mpr ⟨hDS, hxD⟩
  let D' : T := ⟨D, hDT⟩
  let σ := Local.Principal.supportStalkMap X.carrier A.val x hxA
  have hzD : Local.Principal.supportStalkMap X.carrier D.val x hxD (u D') = 0 := by
    apply RingHom.mem_ker.mp
    exact hu D'
  have hzA : σ (u D') = 0 := by
    rw [← NestedSupportStalk.apply_comp X.carrier A.val D.val hAD x hxA hxD (u D'), hzD, map_zero]
  apply hfA
  change σ.hom (∏ D : T, u D) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ D') hzA

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportAvoidance
