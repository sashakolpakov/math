import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Fiber Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberVanishing

noncomputable section

/-! Actual fiber cohomology vanishing gives exactness of the finite
model after the same base change, with its native section-ring action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

universe u

theorem model_baseChange_exactAt_of_fiber_vanishing
    {X Y S T : Scheme.{u}} [Y.IsSeparated]
    (a : Y ⟶ X) (f : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : a ≫ f = ρ ≫ g) (M : X.Modules)
    [((Scheme.Modules.pullback a).obj M).IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (ha : ∀ i, IsAffineOpen (a ⁻¹ᵁ U i))
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U) (n : ℕ)
    [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h M U φ) n]
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback a).obj M) n)] :
    (((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).ExactAt n := by
  apply (exactAt_iff_of_quasiIsoAt
    (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h M U φ) n).mpr
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e := SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv ρ ((Scheme.Modules.pullback a).obj M)
    (fun i => a ⁻¹ᵁ U i) (hU.comap a.base.hom) ha n
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact e.injective.subsingleton

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FiberVanishing
