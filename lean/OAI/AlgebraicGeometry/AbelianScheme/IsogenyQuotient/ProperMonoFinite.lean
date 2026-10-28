import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints

/-! # Proper Mono Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperMonoFinite.Construction

noncomputable section

/-! A proper monomorphism of schemes is finite: each geometric lift
set is a subsingleton, so properness upgrades quasi-finiteness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints.Construction

universe u
theorem proper_mono_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Mono f] : IsFinite f := by
  have : LocallyQuasiFinite f := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    have : Subsingleton {x : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ X //
        x ≫ f = Picard.Homomorphisms.FiniteGeometricPoints.Construction.geometricResiduePoint Y y} := by
      constructor
      intro a b
      exact Subtype.ext ((cancel_mono f).mp (a.property.trans b.property.symm))
    exact Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_preimage_of_finite_geometric_lifts f y
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperMonoFinite.Construction
