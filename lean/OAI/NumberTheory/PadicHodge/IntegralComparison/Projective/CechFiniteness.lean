import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees

/-! # Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechFiniteness

noncomputable section

/-! Finiteness of the original affine-cover Čech cohomology on a projective scheme. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
  (hprojective : Projectivity.Construction.ProjectiveOver R f)
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
  (hUaff : ∀ i, IsAffineOpen (U i))

include hprojective hU hUaff in
theorem finite (n : ℕ) :
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤) ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex f M U).homology n) := by
  let : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) :=
    CoherentFiniteness.base_cohomology_finite R f hprojective M n
  exact Module.Finite.equiv (AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.baseCechHomologyAffineHLinearEquiv f M U hU hUaff n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechFiniteness
