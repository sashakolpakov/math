import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces

/-! # Degree Scalar Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeScalarRestriction.GradedModules

noncomputable section

/-! Restricting coefficient scalars commutes with the actual homogeneous pieces of principal module localizations. -/

universe u v w t

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {M : Type t} [AddCommGroup M] [Module R M] [Module S M] [Module A M]
  [IsScalarTower R S M] [IsScalarTower R A M] [IsScalarTower S A M]

theorem localizedDegreePiece_restrictScalars (ℳ : ℤ → Submodule S M) (a : A) (e d : ℤ) :
    DegreePieces.GradedModules.localizedDegreePiece (fun i => (ℳ i).restrictScalars R) a e d =
      (DegreePieces.GradedModules.localizedDegreePiece ℳ a e d).restrictScalars R := by
  unfold DegreePieces.GradedModules.localizedDegreePiece
  rw [Submodule.restrictScalars_iSup]
  apply iSup_congr
  intro k
  unfold DegreePieces.GradedModules.localizedDegreeStage
  rw [Submodule.restrictScalars_map]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeScalarRestriction.GradedModules
