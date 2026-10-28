import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.IdealUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedRepresentation

/-! # Truncation Reconstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Truncating all-degree quotient data and regenerating recovers its actual ideal
whenever it is generated in the retained degrees. The finite parameter map
then distinguishes all such data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} {r : ℕ → ℕ}
variable (D : GradedQuotientFamilies.GradedQuotientData R σ r)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GradedQuotientFamilies.GradedQuotientData.truncate_generatedIdeal (B : ℕ)
    (hB : D.relations.lowDegreeIdeal B = D.ideal.toIdeal) :
    (D.truncate B).generatedIdeal = D.ideal := by
  apply (D.truncate B).generatedIdeal_unique D.ideal
  · have he : GradedIdealReconstruction.homogeneousIdealRelations D.ideal = D.relations :=
      GradedIdealReconstruction.homogeneousIdealRelationsEquiv.right_inv D.relations
    rw [he]
    exact hB
  · intro d
    exact D.degreeRelations_eq d

theorem GradedQuotientFamilies.GradedQuotientData.ideal_fg_of_lowDegreeIdeal_eq [Finite σ] (B : ℕ)
    (hB : D.relations.lowDegreeIdeal B = D.ideal.toIdeal) : D.ideal.toIdeal.FG := by
  rw [← D.truncate_generatedIdeal B hB]
  exact (D.truncate B).generatedIdeal_fg

theorem GradedQuotientFamilies.GradedQuotientData.ext_of_ideal_eq (E : GradedQuotientFamilies.GradedQuotientData R σ r) (h : D.ideal = E.ideal) : D = E := by
  have hq : D.quotient = E.quotient := by
    funext d
    apply Module.Grassmannian.ext
    exact (D.degreeRelations_eq d).symm.trans
      ((congrArg (fun I => Homogeneous.IdealIncidence.homogeneousDegreeRelations I d) h).trans (E.degreeRelations_eq d))
  cases D
  cases E
  cases hq
  rfl

theorem GradedQuotientFamilies.GradedQuotientData.ext_of_truncate_eq (E : GradedQuotientFamilies.GradedQuotientData R σ r) (B : ℕ)
    (hD : D.relations.lowDegreeIdeal B = D.ideal.toIdeal)
    (hE : E.relations.lowDegreeIdeal B = E.ideal.toIdeal)
    (h : D.truncate B = E.truncate B) : D = E :=
  D.ext_of_ideal_eq E ((D.truncate_generatedIdeal B hD).symm.trans
    ((congrArg Truncated.GradedClassification.TruncatedGradedQuotientData.generatedIdeal h).trans (E.truncate_generatedIdeal B hE)))

end

universe u v

variable {σ : Type v} [Finite σ] {r : ℕ → ℕ} {B : ℕ}
variable {R : CommRingCat.{max u v}} {S : Scheme.{max u v}} (f : Spec R ⟶ S)

theorem TruncationReconstruction.boundedGradedParameter_injective : Function.Injective
    (fun D : {D : GradedQuotientFamilies.GradedQuotientData R σ r // D.relations.lowDegreeIdeal B = D.ideal.toIdeal} =>
      (D.val.truncate B).classifyingMap f) := by
  intro D E h
  apply Subtype.ext
  apply D.val.ext_of_truncate_eq E.val B D.property E.property
  exact Truncated.GradedClassification.TruncatedGradedQuotientData.classifyingMap_injective f h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
