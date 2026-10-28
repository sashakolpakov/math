import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints

/-! # Proper Subfunctor Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperSubfunctorFinite.Construction

noncomputable section

/-! A proper scheme which embeds into a finite scheme over the base
is itself finite. The proof retains its full scheme structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints.Construction

universe u

theorem proper_subfunctor_of_finite_isFinite
    {S : Scheme.{u}} {K H : Over S} [IsProper K.hom] [IsFinite H.hom]
    (c : K ⟶ H) [Mono c] : IsFinite K.hom := by
  have : LocallyQuasiFinite K.hom := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro s
    let t := Picard.Homomorphisms.FiniteGeometricPoints.Construction.geometricResiduePoint S s
    have : Finite (Over.mk t ⟶ H) := Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_overPoints H t
    have : Finite (Over.mk t ⟶ K) :=
      Finite.of_injective (fun x : Over.mk t ⟶ K => x ≫ c) (fun _ _ h => (cancel_mono c).mp h)
    have : Finite {x : Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ K.left //
        x ≫ K.hom = t} := Finite.of_equiv _ (Picard.Homomorphisms.FiniteGeometricPoints.Construction.overPointsEquiv K t)
    exact Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_preimage_of_finite_geometric_lifts K.hom s
  exact IsFinite.of_isProper_of_locallyQuasiFinite K.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProperSubfunctorFinite.Construction
