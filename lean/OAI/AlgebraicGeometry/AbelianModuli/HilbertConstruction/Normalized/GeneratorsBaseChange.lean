import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.HomogeneousGenerators

/-! # Generators Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratorsBaseChange

noncomputable section

/-! The explicit generators on a Grassmann chart commute with arbitrary coefficient homomorphisms. -/

universe u

variable {R A : Type u} [CommRing R] [CommRing A] {n N : ℕ}
variable (φ : R →+* A)

theorem homogeneousLiftedCoordinates_coefficientMap
    (p : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) :
    Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N A
        ⟨MvPolynomial.map φ p.val, p.property.map φ⟩ =
      φ ∘ Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R p := by
  funext j
  exact congrFun (Homogeneous.Coordinates.homogeneousCoordinates_coefficientMap R (Fin (n + 1)) N φ p) j.down

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (Q : Matrix ι (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) R)

omit [DecidableEq ι] in
theorem normalizedHomogeneousGenerator_map
    (j : ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) :
    MvPolynomial.map φ (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).val =
      (HomogeneousGenerators.normalizedHomogeneousGenerator a (Q.map φ) j).val := by
  have h : (⟨MvPolynomial.map φ (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).val,
      (HomogeneousGenerators.normalizedHomogeneousGenerator a Q j).property.map φ⟩ :
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A N) =
      HomogeneousGenerators.normalizedHomogeneousGenerator a (Q.map φ) j := by
    apply (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N A).injective
    rw [homogeneousLiftedCoordinates_coefficientMap]
    simp only [HomogeneousGenerators.normalizedHomogeneousGenerator, LinearEquiv.apply_symm_apply]
    funext i
    exact congrArg (fun K => K i j) (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix_map φ a Q)
  exact congrArg Subtype.val h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratorsBaseChange
