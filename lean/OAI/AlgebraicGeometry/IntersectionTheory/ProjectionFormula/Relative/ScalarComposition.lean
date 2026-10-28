import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI

/-! # Scalar Composition -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ScalarComposition

noncomputable section

/-! Coefficient maps compose functorially on the actual relative
projective spectra, including split coefficient specializations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem graded_comp (f : R →+* S) (g : S →+* T) (n : ℕ) :
    ProjectiveI.Scalars.graded (g.comp f) n = (ProjectiveI.Scalars.graded g n).comp (ProjectiveI.Scalars.graded f n) := by
  apply GradedRingHom.ext
  intro p
  exact (MvPolynomial.map_map f g p).symm

theorem graded_id (n : ℕ) : ProjectiveI.Scalars.graded (RingHom.id R) n = GradedRingHom.id (ProjectiveLinear.grading R n) := by
  apply GradedRingHom.ext
  intro p
  exact MvPolynomial.map_id p

theorem map_comp (f : R →+* S) (g : S →+* T) (n : ℕ) :
    ProjectiveI.Scalars.map g n ≫ ProjectiveI.Scalars.map f n =
      ProjectiveI.Scalars.map (g.comp f) n := by
  unfold ProjectiveI.Scalars.map
  rw [← Proj.map_comp]
  simp only [← graded_comp]

theorem map_id (n : ℕ) : ProjectiveI.Scalars.map (RingHom.id R) n = 𝟙 (ProjectiveLinear.space R n) := by
  unfold ProjectiveI.Scalars.map
  simp only [graded_id, Proj.map_id]

theorem map_split (f : R →+* S) (g : S →+* R) (h : g.comp f = RingHom.id R) (n : ℕ) :
    ProjectiveI.Scalars.map g n ≫ ProjectiveI.Scalars.map f n = 𝟙 (ProjectiveLinear.space R n) := by
  rw [ScalarComposition.map_comp, h, ScalarComposition.map_id]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ScalarComposition
