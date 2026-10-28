import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ComponentFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ClosedCarrierBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels

/-! # Component Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restrict the remaining native boundary labels to a distinguished boundary component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.componentCarrier
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} [Fintype β]
    {D : Option β → X.IdealSheafData} {L : List (Finset (Option β))}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas ((D none).subschemeι ≫ f)
      (fun j => (D (some j)).comap (D none).subschemeι) [Finset.univ] := by
  apply A.dropFirst.closedCarrier (D none)
  intro i
  let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  have he := congrArg (fun K : Ideal Γ(X, A.opens i) =>
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Γ(X, A.opens i) ⧸ K))
      (fun j => Ideal.Quotient.mk K (A.equations i (some j)))) (A.component i none)
  exact he.mpr (A.boundary i).componentFiber

end

end OAI.AlgebraicGeometry.Resolution.Blowups
