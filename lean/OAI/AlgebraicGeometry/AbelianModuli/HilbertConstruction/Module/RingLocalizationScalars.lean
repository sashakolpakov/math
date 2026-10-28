import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RingLocalization

/-! # Ring Localization Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RingLocalizationScalars

noncomputable section

/-! The module-to-ring localization equivalence preserves the full polynomial scalar action. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RingLocalization.GradedModules

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

theorem moduleRingLocalizationEquiv_scalar (g a : A) (x : HilbertScheme.Presentations.Module.Fractions.GradedModules.AwayModule g B) :
    HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B g (a • x) =
      algebraMap A (Localization.Away (algebraMap A B g)) a * HilbertScheme.Presentations.Module.RingLocalization.GradedModules.moduleRingLocalizationEquiv (R := R) B g x := by
  have he := (IsLocalizedModule.iso (Submonoid.powers g)
    (IsScalarTower.toAlgHom A B (Localization.Away (algebraMap A B g))).toLinearMap).map_smul a x
  exact he.trans (Algebra.smul_def a _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RingLocalizationScalars
