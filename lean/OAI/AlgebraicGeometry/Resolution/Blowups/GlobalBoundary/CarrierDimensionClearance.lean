import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearanceSolver
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Component
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CartierDimension

/-! # Carrier Dimension Clearance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierDimensionClearance.Construction

noncomputable section

/-! A genuine lower-dimension induction hypothesis clears a distinguished integral boundary carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_boundary_carrier_clearance_of_dimension_solver
    (d : ℕ)
    (hsolve : ∀ (Y : Scheme) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
      (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth g], topologicalKrullDim Y ≤ d →
      ∀ (γ : Type) [Fintype γ] (E : γ → Y.IdealSheafData),
      (∀ j, E j ≠ ⊥) → Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g E [Finset.univ] →
      ∀ (C : Y.IdealSheafData), C ≠ ⊥ → ∀ (b : ℕ), 0 < b →
      ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b Y g C, T.boundaryCompatible γ E)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (hd : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (J H : X.IdealSheafData) [IsIntegral H.subscheme] (n : ℕ)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
      (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ]) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)),
      U.integralCenters ∧
      U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (U.toBase ≫ f) (U.transformIdeal J (n + 1)) n ⊔ U.transformIdeal H 1 = ⊤ := by
  have hH : H ≠ ⊥ := A.component_ne_bot none
  have hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H := A.component_locallyPrincipal none
  let : Smooth (H.subschemeι ≫ f) := A.component_smooth none
  apply CarrierClearanceSolver.Construction.exists_global_boundary_carrier_clearance_of_lower_solver f J H hH hlocal n D A
  intro C hC
  let : IsLocallyNoetherian H.subscheme := LocallyOfFiniteType.isLocallyNoetherian H.subschemeι
  let : CompactSpace H.subscheme := QuasiCompact.compactSpace_of_compactSpace H.subschemeι
  let B : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (H.subschemeι ≫ f)
      (fun j => (D j).comap H.subschemeι) [Finset.univ] := A.componentCarrier
  exact hsolve H.subscheme (H.subschemeι ≫ f)
    (Global.CartierDimension.Construction.locallyPrincipal_subscheme_dimension_le H hH hlocal d hd) β
    (fun j => (D j).comap H.subschemeι) B.component_ne_bot B C hC
    (n + 1).factorial (Nat.factorial_pos _)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierDimensionClearance.Construction
