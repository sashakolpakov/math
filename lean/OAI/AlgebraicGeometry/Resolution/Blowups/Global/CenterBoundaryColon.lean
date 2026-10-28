import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterTransverseColon
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Component
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFlatPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility

/-! # Center Boundary Colon -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! The native ideal quotient by a boundary component detects the center components it does not contain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundary_colon_ideal
    {X : Scheme} [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [DecidableEq β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (j : β) (i : A.indices) :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon I (D j)).ideal (A.opens i) =
      if j ∈ A.divided i then ⊤ else I.ideal (A.opens i) := by
  let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  rw [NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal, A.component i j]
  by_cases hj : j ∈ A.divided i
  · rw [ite_eq_left hj]
    apply (Submodule.colon_eq_top_iff_subset _).mpr
    exact Ideal.span_le.mpr (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ A.contained i j hj)
  · rw [ite_eq_right hj]
    exact (A.center i).transverse_colon (.of Γ(X, A.opens i)) (I.ideal (A.opens i)) j hj

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundary_colon_comap_flat
    {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (j : β) (q : Y ⟶ X) [Flat q] :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon I (D j)).comap q =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (I.comap q) ((D j).comap q) :=
  Locally.PrincipalColonFlatPullback.Construction.locallyPrincipal_noetherianIdealSheafColon_comap_flat I (D j)
    (A.boundaryAtlas.component_locallyPrincipal j) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
