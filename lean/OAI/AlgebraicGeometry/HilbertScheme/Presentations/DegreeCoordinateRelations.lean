import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension

/-! # Degree Coordinate Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert

noncomputable section

/-! Homogeneous degree relations in fixed monomial coordinates commute
with arbitrary coefficient-ring base change. -/

open TensorProduct _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian

universe u
variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

def degreeCoordinateRelations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Submodule R (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d → R) :=
  (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).map (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d).equivFun.toLinearMap

theorem coordinateDegreeBasis_map (φ : R →+* A) (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis A n d).equivFun ⟨MvPolynomial.map φ f.val, f.property.map φ⟩ =
      φ ∘ (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d).equivFun f := by
  funext m
  change AddMonoidAlgebra.coeff (MvPolynomial.map φ f.val) m.down.val = φ (AddMonoidAlgebra.coeff f.val m.down.val)
  exact MvPolynomial.coeff_map φ f.val m.down.val

theorem degreeCoordinateRelations_baseChange [Algebra R A]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) (degreeCoordinateRelations I d) =
      degreeCoordinateRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨f, hf, rfl⟩ := hv
    refine ⟨⟨MvPolynomial.map (algebraMap R A) f.val, f.property.map _⟩,
      Ideal.mem_map_of_mem _ hf, coordinateDegreeBasis_map (algebraMap R A) d f⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨z, hz⟩ := RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap_surjective (S := A) I d ⟨f, hf⟩
    have hm : (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis A n d).equivFun (RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d z).val ∈
        Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) (degreeCoordinateRelations I d) := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul s g =>
        have he : (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis A n d).equivFun
            (RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d (s ⊗ₜ[R] g)).val =
            s • ((algebraMap R A) ∘ (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n d).equivFun g.val) := by
          funext m
          change AddMonoidAlgebra.coeff (RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d (s ⊗ₜ[R] g)).val.val m.down.val =
            s • algebraMap R A (AddMonoidAlgebra.coeff g.val.val m.down.val)
          rw [RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap_tmul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, MvPolynomial.coeff_map]
        rw [he]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨_, ⟨g.val, g.property, rfl⟩, rfl⟩
      | add z w hz hw =>
        simpa only [map_add, Submodule.coe_add] using Submodule.add_mem _ hz hw
    have he : (RelationsBaseChangeMap.GradedHilbert.degreeRelationsBaseChangeMap (S := A) I d z).val = f := congrArg Subtype.val hz
    rwa [he] at hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert
