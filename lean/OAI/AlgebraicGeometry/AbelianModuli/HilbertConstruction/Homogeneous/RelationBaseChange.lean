import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IdealIncidence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap

/-! # Relation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RelationBaseChange

noncomputable section

/-!
In lifted monomial coordinates, degree relations of an extended homogeneous
ideal are exactly coefficient extensions of the original relation submodule.
This identifies geometric quotient base change with the Grassmannian API.
-/

open TensorProduct
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem homogeneousLiftedCoordinates_map (d : ℕ) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) :
    QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A
      ⟨MvPolynomial.map (algebraMap R A) p.val, p.property.map (algebraMap R A)⟩ =
        algebraMap R A ∘ QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R p := by
  funext b
  exact congrFun (Coordinates.homogeneousCoordinates_coefficientMap R (Fin (n + 1)) d
    (algebraMap R A) p) b.down

theorem homogeneousLiftedRelations_baseChange (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d).map
      (QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A).toLinearMap =
        HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A)
          ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).map
            (QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R).toLinearMap) := by
  let eR := QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R
  let eA := QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A
  let M := HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A)
    ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).map eR.toLinearMap)
  have hmem (z : A ⊗[R] HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) :
      eA (HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d z).val ∈ M := by
    induction z using TensorProduct.inductionOn with
    | tmul a p =>
        have he : (HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d (a ⊗ₜ[R] p)).val =
            a • (⟨MvPolynomial.map (algebraMap R A) p.val.val,
              p.val.property.map (algebraMap R A)⟩ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n d) :=
          Subtype.ext (HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap_tmul I d a p)
        rw [he, map_smul]
        change a • QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A _ ∈ M
        rw [homogeneousLiftedCoordinates_map]
        exact M.smul_mem a (Submodule.subset_span
          ⟨eR p.val, Submodule.mem_map.mpr ⟨p.val, p.property, rfl⟩, rfl⟩)
    | add z w hz hw =>
        simp only [map_add, Submodule.coe_add]
        exact M.add_mem hz hw
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ := HilbertScheme.Presentations.RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap_surjective (S := A) I d ⟨p, hp⟩
    have h := hmem z
    rw [hz] at h
    exact h
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    let p' : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n d := ⟨MvPolynomial.map (algebraMap R A) p.val,
      p.property.map (algebraMap R A)⟩
    have hp' : p' ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d :=
      Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R A)) hp
    exact ⟨p', hp', homogeneousLiftedCoordinates_map d p⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RelationBaseChange
