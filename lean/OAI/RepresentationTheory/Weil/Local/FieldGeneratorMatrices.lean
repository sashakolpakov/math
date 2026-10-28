import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Field Generator Matrices -/

namespace OAI.RepresentationTheory.Weil.Local.FieldGeneratorMatrices.Construction

noncomputable section

/-! Generator matrices, determinants, and coordinates under a field isomorphism. -/

open _root_.Matrix

variable {k l : Type} [Field k] [Field l]

def fieldGeneralLinear (e : k ≃+* l) (n : ℕ) : FunctionsMetaplectic.Construction.GeneralLinear k n →* FunctionsMetaplectic.Construction.GeneralLinear l n :=
  Units.map e.toRingHom.mapMatrix.toMonoidHom

def fieldSymmetricMatrix (e : k ≃+* l) {n : ℕ} (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.SymmetricMatrix l n :=
  ⟨B.val.map e, B.property.map e⟩

theorem fieldGeneralLinear_val (e : k ≃+* l) {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (fieldGeneralLinear e n A : Matrix (Fin n) (Fin n) l) = A.val.map e := rfl

theorem fieldSymplecticMap_levi (e : k ≃+* l) {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    FieldFourier.Construction.fieldSymplecticMap e n (Generators.Construction.leviSymplectic A) = Generators.Construction.leviSymplectic (fieldGeneralLinear e n A) := by
  apply Subtype.ext
  change (fromBlocks A.val 0 0 (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose).map e =
    fromBlocks (A.val.map e) 0 0 ((↑(A⁻¹) : Matrix (Fin n) (Fin n) k).map e).transpose
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks]

theorem fieldSymplecticMap_quadratic (e : k ≃+* l) {n : ℕ} (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FieldFourier.Construction.fieldSymplecticMap e n (Generators.Construction.quadraticSymplectic B) = Generators.Construction.quadraticSymplectic (fieldSymmetricMatrix e B) := by
  apply Subtype.ext
  change (fromBlocks 1 0 B.val 1).map e = fromBlocks 1 0 (B.val.map e) 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, Matrix.one_apply]

theorem fieldSymplecticMap_weyl (e : k ≃+* l) (n : ℕ) :
    FieldFourier.Construction.fieldSymplecticMap e n (Generators.Construction.weylSymplectic k n) = Generators.Construction.weylSymplectic l n := by
  apply Subtype.ext
  change (↑(Generators.Construction.weylSymplectic k n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).map e =
    (↑(Generators.Construction.weylSymplectic l n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) l)
  rw [Generators.Construction.weylSymplectic_matrix, Generators.Construction.weylSymplectic_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, Matrix.one_apply]

theorem fieldGeneralLinear_determinant
    {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    FunctionsMetaplectic.Construction.determinantUnit l (fieldGeneralLinear e n A) = Units.map e.toMonoidHom (FunctionsMetaplectic.Construction.determinantUnit k A) := by
  apply Units.ext
  change det (A.val.map e) = e (det A.val)
  exact (RingHom.map_det e.toRingHom A.val).symm

theorem fieldGeneralLinear_inverse_mulVec (e : k ≃+* l) {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (x : FunctionsMetaplectic.Construction.Position k n) :
    (fun i => e.symm (mulVec (↑((fieldGeneralLinear e n A)⁻¹) : Matrix (Fin n) (Fin n) l)
      (fun j => e (x j)) i)) = mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x := by
  ext i
  change e.symm (∑ j, e ((↑(A⁻¹) : Matrix (Fin n) (Fin n) k) i j) * e (x j)) =
    ∑ j, (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) i j * x j
  rw [map_sum]
  simp only [map_mul, RingEquiv.symm_apply_apply]

theorem fieldSymmetricMatrix_quadratic (e : k ≃+* l) {n : ℕ} (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n)
    (x : FunctionsMetaplectic.Construction.Position k n) :
    e.symm ((∑ i, ∑ j, e (x i) * (fieldSymmetricMatrix e B).val i j * e (x j)) / 2) =
      (∑ i, ∑ j, x i * B.val i j * x j) / 2 := by
  simp only [map_div₀, map_sum, map_mul, map_ofNat, fieldSymmetricMatrix, Matrix.map_apply,
    RingEquiv.symm_apply_apply]

end

end OAI.RepresentationTheory.Weil.Local.FieldGeneratorMatrices.Construction
