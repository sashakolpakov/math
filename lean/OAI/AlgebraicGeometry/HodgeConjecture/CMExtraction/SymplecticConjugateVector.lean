import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearActionMatrices

/-! # Symplectic Conjugate Vector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector.TestTransport

noncomputable section

/-! Recover an original vector action from its conjugated symplectic coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

theorem symplectic_conjugate_vector {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (S T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (x y : I ⊕ I → R)
    (h : S.val *ᵥ x = T.val *ᵥ (S.val *ᵥ y)) :
    (S⁻¹ * T * S).val *ᵥ y = x := by
  have hs : (S⁻¹).val * S.val = 1 := congrArg Subtype.val (inv_mul_cancel S)
  change ((S⁻¹).val * T.val * S.val) *ᵥ y = x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← h,
    Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]

theorem symplectic_vector_of_conjugation {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (A S T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (x y : I ⊕ I → R) (hA : A = S⁻¹ * T * S)
    (h : S.val *ᵥ x = T.val *ᵥ (S.val *ᵥ y)) : A.val *ᵥ y = x := by
  rw [hA]
  exact symplectic_conjugate_vector S T x y h

theorem symplectic_projected_column {I R K : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing K] (f : R →+* K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (x y : I ⊕ I → K)
    (j : I ⊕ I) (hx : x = Pi.single j 1) (h : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g).val *ᵥ x = y) (i : I ⊕ I) :
    f (g.val i j) = y i :=
  LinearActionMatrices.TestTransport.matrix_column_from_vector (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g).val x y j hx h i

theorem symplectic_map_compare_entries {I R K L : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing K] [CommRing L] (f : R →+* L) (h : K →+* L)
    (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp h a) (i j : I ⊕ I) :
    f (g.val i j) = h (a.val i j) :=
  congrArg (fun A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I L => A.val i j) he

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector.TestTransport
