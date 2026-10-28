import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ComponentAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.PrincipalEquations
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf

/-! # Component -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A native boundary atlas supplies nonzero smooth locally principal components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.component_locallyPrincipal
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (j : β) : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (D j) := by
  intro x
  have hx : x ∈ ⨆ i, (A.opens i).1 := by rw [A.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨A.opens i, hi, A.equations i j, A.component i j⟩

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.component_smooth
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (j : β) : Smooth ((D j).subschemeι ≫ f) := by
  classical
  have h := A.intersection_smooth f D L {j}
  have he : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D {j} = D j := Finset.sup_singleton
  rwa [he] at h

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.component_ne_bot
    {X : Scheme} [Nonempty X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (j : β) : D j ≠ ⊥ := by
  classical
  intro hzero
  obtain ⟨i, p, _⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec A.opens A.cover (Classical.choice inferInstance)
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  obtain ⟨C⟩ := A.boundary i p
  let : Algebra ℂ C.carrier := C.algebra
  let : Nontrivial C.carrier := C.point.nontrivial
  have hz : A.equations i j = 0 := by
    have h := A.component i j
    rw [hzero] at h
    change ⊥ = Ideal.span {A.equations i j} at h
    exact Ideal.mem_bot.mp (h.symm ▸ Ideal.mem_span_singleton_self (A.equations i j))
  have hne := nonZeroDivisors.ne_zero (C.model.component_regular j).mem_nonZeroDivisors
  exact hne (by simp only [hz, map_zero])

end

end OAI.AlgebraicGeometry.Resolution.Blowups
