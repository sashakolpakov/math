import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinatePointPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointPresentationFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PresentationComposition

/-! # Coordinate Presentation Factor Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Specializing an ordinary-coordinate kernel and then embedding it
in an ambient point preserves the actual carrier and composed inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

attribute [local instance] Classical.propDecidable

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_geometric_presentation_factor
    {B : Over (Spec (.of R))} {D : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))}
    (i : A.X ⟶ B)
    (j : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).obj B ⟶ D)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))
    (V : Submodule (ZMod q) (Fin 2 → ZMod q)) (flag : Bool)
    (hV : J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)) = V)
    (hflag : decide (SubspaceCounts.Construction.identityLine ≤ J) = flag)
    (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))) (z : T ⟶ D) :
    let K := ((C.finiteFlatKernel R L q A J).toKernelPresentation.postcomp i).pullback
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))
    let Q := (C.geometricSpecialKernel R L q A ρ V flag).postcomp
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).map i ≫ j)
    (∃ h : T ⟶ K.carrier, h ≫ K.inclusion ≫ j = z) ↔
      ∃ h : T ⟶ Q.carrier, h ≫ Q.inclusion = z := by
  have hp := (C.finiteFlatKernel_geometricPointPresentation R L q A ρ i j J).trans
    (congrArg₂ (fun U b => (C.geometricSpecialKernel R L q A ρ U b).postcomp
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).map i ≫ j)) hV hflag)
  exact Intrinsic.Neighbors.KernelPresentation.point_factor_iff _ _ hp T z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
