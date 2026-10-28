import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteAnisotropy
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm

/-! # Isometry Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding

noncomputable section

/-! Isometries of the actual E-Hermitian matrices remain isometries
on every complex embedding block, by sesquilinearity and the standard
basis. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

omit [NumberField E] [NumberField.IsCMField E] in
theorem embedding_basisFun (σ : E →ₐ[ℚ] ℂ) (i : Fin 3) :
    (fun j => σ (Pi.basisFun E (Fin 3) i j)) = Pi.basisFun ℂ (Fin 3) i := by
  classical
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply]

theorem hermitianIsometry_embedding
    (H K : Matrix (Fin 3) (Fin 3) E) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian K (u x) (u y) =
      Datum.RankThreePELDatum.matrixHermitian H x y)
    (σ : E →ₐ[ℚ] ℂ) (x y : Fin 3 → ℂ) :
    Complex.HermitianMatrixForm.complexHermitianMatrixForm (K.map σ)
      (((LinearMap.toMatrix' u).map σ).mulVec x) (((LinearMap.toMatrix' u).map σ).mulVec y) =
        Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map σ) x y := by
  let m := Matrix.toLin' ((LinearMap.toMatrix' u).map σ)
  have hm (i : Fin 3) : m (Pi.basisFun ℂ (Fin 3) i) =
      fun j => σ (u (Pi.basisFun E (Fin 3) i) j) := by
    rw [← embedding_basisFun σ i]
    funext j
    exact EmbeddingMatrixTransport.embeddedMatrix_apply u σ (Pi.basisFun E (Fin 3) i) j
  have hF : ((Complex.HermitianMatrixForm.complexHermitianMatrixForm (K.map σ)).comp m).compl₂ m =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map σ) := by
    apply (Pi.basisFun ℂ (Fin 3)).ext
    intro i
    apply (Pi.basisFun ℂ (Fin 3)).ext
    intro j
    change Complex.HermitianMatrixForm.complexHermitianMatrixForm (K.map σ) (m (Pi.basisFun ℂ (Fin 3) i))
      (m (Pi.basisFun ℂ (Fin 3) j)) = _
    rw [hm, hm, ← embedding_basisFun σ i, ← embedding_basisFun σ j,
      Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply, Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply]
    exact (DefiniteAnisotropy.matrixHermitian_embedding σ K (u (Pi.basisFun E (Fin 3) i))
      (u (Pi.basisFun E (Fin 3) j))).symm.trans
        ((congrArg σ (hu (Pi.basisFun E (Fin 3) i) (Pi.basisFun E (Fin 3) j))).trans
          (DefiniteAnisotropy.matrixHermitian_embedding σ H (Pi.basisFun E (Fin 3) i) (Pi.basisFun E (Fin 3) j)))
  exact LinearMap.congr_fun (LinearMap.congr_fun hF x) y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
