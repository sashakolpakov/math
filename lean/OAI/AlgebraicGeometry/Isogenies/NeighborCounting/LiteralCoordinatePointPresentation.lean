import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinatePointPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PresentationComposition

/-! # Literal Coordinate Point Presentation -/

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

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel_literal_geometricPointPresentation
    {B : Over (Spec (.of R))} {D : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))}
    (i : A.X ⟶ B)
    (j : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).obj B ⟶ D)
    (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    (show Intrinsic.Neighbors.KernelPresentation ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).obj B) from
      ⟨(Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).obj
          (C.finiteFlatKernel R L q A J).carrier,
        (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).map
          ((C.finiteFlatKernel R L q A J).inclusion ≫ i)⟩).postcomp j =
    (C.geometricSpecialKernel R L q A ρ
      (J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)))
      (decide (SubspaceCounts.Construction.identityLine ≤ J))).postcomp
        ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).map i ≫ j) :=
  C.finiteFlatKernel_geometricPointPresentation R L q A ρ i j J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
