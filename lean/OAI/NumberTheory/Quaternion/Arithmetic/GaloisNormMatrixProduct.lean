import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm
import OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveDerivative

/-! # Galois Norm Matrix Product -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GaloisNormMatrixProduct

noncomputable section

/-! The matrix of a commuting Galois norm can be evaluated as a fixed
ordered product in any commutative coefficient algebra. -/

open scoped Classical

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {n : ℕ}

theorem galoisPointNorm_mapped_matrix {A : Type*} [CommRing A] (f : E →+* A)
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.Points (algebraMap F E))
    (hc : ∀ σ τ : E ≃ₐ[F] E, Commute (GaloisPoints.galoisPointsHom G σ g) (GaloisPoints.galoisPointsHom G τ g)) :
    (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) (GaloisNorm.galoisPointNorm G g hc)).map f =
      ((Finset.univ : Finset (E ≃ₐ[F] E)).toList.map
        (fun σ => (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) g).map (f.comp σ.toRingHom))).prod := by
  have hp := ProductCurveDerivative.list_prod_eq_noncommProd Finset.univ (Finset.coe_toList _)
    (fun σ => GaloisPoints.galoisPointsHom G σ g) hc
  change ((Finset.univ : Finset (E ≃ₐ[F] E)).toList.map
    (fun σ => GaloisPoints.galoisPointsHom G σ g)).prod = GaloisNorm.galoisPointNorm G g hc at hp
  let φ := f.mapMatrix.toMonoidHom.comp (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E))
  change φ (GaloisNorm.galoisPointNorm G g hc) = _
  rw [← hp, map_list_prod, List.map_map]
  rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.GaloisNormMatrixProduct
