import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Augmented Residue Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedResidueMap

noncomputable section

/-! A local algebra with a rational augmentation has its coefficient
field as residue field. Local maps between such algebras induce separable maps. -/

set_option backward.isDefEq.respectTransparency false

open IsLocalRing

universe u v w

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
  (ε : R →ₐ[K] K)

include ε

theorem coefficients_surjective : Function.Surjective (algebraMap K (ResidueField R)) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨ε r, ?_⟩
  change Ideal.Quotient.mk (maximalIdeal R) (algebraMap K R (ε r)) = Ideal.Quotient.mk (maximalIdeal R) r
  apply Ideal.Quotient.eq.mpr
  rw [← AugmentedRegularJet.ideal_eq ε]
  change ε (algebraMap K R (ε r) - r) = 0
  simp

variable {A : Type w} [CommRing A] [Algebra K A] [IsLocalRing A]
  (g : A →ₐ[K] R) [IsLocalHom g.toRingHom]

theorem map_surjective : Function.Surjective (ResidueField.map g.toRingHom) := by
  intro z
  obtain ⟨c, rfl⟩ := coefficients_surjective ε z
  refine ⟨algebraMap K (ResidueField A) c, ?_⟩
  change ResidueField.map g.toRingHom (residue A (algebraMap K A c)) = residue R (algebraMap K R c)
  rw [ResidueField.map_residue]
  exact congrArg (residue R) (g.commutes c)

theorem separable :
    letI := g.toRingHom.toAlgebra
    Algebra.IsSeparable (ResidueField A) (ResidueField R) := by
  let := g.toRingHom.toAlgebra
  constructor
  intro r
  obtain ⟨a, rfl⟩ := map_surjective ε g r
  exact isSeparable_algebraMap a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedResidueMap
