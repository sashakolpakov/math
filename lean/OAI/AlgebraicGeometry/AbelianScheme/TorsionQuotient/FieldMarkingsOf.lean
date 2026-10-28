import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Points

/-! # Field Markings Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FieldMarkingsOf.FieldMarkings

/-! An injective homomorphism over a field gives an actual distinct marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem field_morphism_epi {K L : Type u} [Field K] [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) : Epi f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact IsogenyQuotient.Geometric.Points.Construction.field_spec_epi φ.hom

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
variable {M : Type u} [Group M] [Fintype M]
variable [IsFinite H.hom] [Etale H.hom]

omit [Fintype M] [IsFinite H.hom] [Etale H.hom] in
theorem distinct_of_injective (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (a : M →* (Over.mk s ⟶ H))
    (ha : Function.Injective a) : EmbeddingParametersIs.EmbeddingParameters.Distinct H M a := by
  intro L hL t x m n hmn
  have : Epi x.left := field_morphism_epi x.left
  have : Epi x := Over.epi_of_epi_left x
  exact ha ((cancel_epi x).mp hmn)

noncomputable def ofInjective (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (a : M →* (Over.mk s ⟶ H))
    (ha : Function.Injective a) : Over.mk s ⟶ EmbeddingParametersIs.EmbeddingParameters.parameter H M :=
  (EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M _).symm ⟨a, distinct_of_injective K s a ha⟩

theorem ofInjective_points (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (a : M →* (Over.mk s ⟶ H))
    (ha : Function.Injective a) :
    (EmbeddingParametersIs.EmbeddingParameters.points H M _ (ofInjective K s a ha)).val = a :=
  congrArg Subtype.val ((EmbeddingParametersIs.EmbeddingParameters.pointsEquiv H M _).apply_symm_apply _)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FieldMarkingsOf.FieldMarkings
