import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.CoherentCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness

/-! # Proper Coherent Coefficient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient.ProperCoherentFiniteness

noncomputable section

/-! # Proper coherent cohomology with the original coefficient action

Properness over a noetherian affine base supplies finiteness through the
actual coherent-support argument. The coefficient identification is the
original global-sections equivalence for the affine base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

theorem base (q : ℕ) :
    letI := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (SheafCohomology.AffineH.Projective.H M q) :=
  HilbertScheme.Presentations.Proper.CoherentCohomology.proper_coherent_cohomologyFinite f M q

theorem coefficient (q : ℕ) :
    letI := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule R f M q
    Module.Finite R (SheafCohomology.AffineH.Projective.H M q) := by
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M q
  let := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule R f M q
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (SheafCohomology.AffineH.Projective.H M q) := base R f M q
  exact Module.Finite.of_surjective
    (NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.baseToCoefficientSemilinear R f M q) Function.surjective_id

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient.ProperCoherentFiniteness
