import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Ambient Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The actual complexification of an E-linear reference map acts on
both embedding blocks by its coefficientwise embedded matrix. -/

open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.referenceAmbientAction (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  LinearEquiv.piCongrRight (fun i => (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings i)).prodCongr
    (EmbeddedLinearGroup.embeddedLinearIso g (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i))))

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.referenceAmbientAction_embedding (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.referenceAmbientAction g (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v) = Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings (g v) := by
  funext i
  apply Prod.ext
  · funext j
    exact EmbeddingMatrixTransport.embeddedMatrix_apply g.toLinearMap (P.embeddings i) v j
  · funext j
    exact EmbeddingMatrixTransport.embeddedMatrix_apply g.toLinearMap (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) v j

theorem Datum.RankThreePELDatum.referenceComplexCoordinates_action (hP : P.IsAdmissible) (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (v : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    P.referenceComplexCoordinates hP ((g.restrictScalars ℚ).toLinearMap.baseChange ℂ v) =
      P.referenceAmbientAction g (P.referenceComplexCoordinates hP v) := by
  let L := (P.referenceComplexCoordinates hP).toLinearMap.comp ((g.restrictScalars ℚ).toLinearMap.baseChange ℂ)
  let R := (P.referenceAmbientAction g).toLinearMap.comp (P.referenceComplexCoordinates hP).toLinearMap
  change L v = R v
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)
  | tmul c v =>
    change P.referenceComplexCoordinates hP (c ⊗ₜ[ℚ] g v) = P.referenceAmbientAction g (P.referenceComplexCoordinates hP (c ⊗ₜ[ℚ] v))
    rw [P.referenceComplexCoordinates_tmul, P.referenceComplexCoordinates_tmul, map_smul, P.referenceAmbientAction_embedding]

end

/-! The paired reference embedding action respects the exact group
operations, including the two inverse identities. -/

variable {E : Type} [Field E] [Algebra ℚ E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem Datum.RankThreePELDatum.referenceAmbientAction_one : P.referenceAmbientAction (1 : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) = 1 := by
  apply LinearEquiv.ext
  intro x
  funext i
  apply Prod.ext
  · change EmbeddedLinearGroup.embeddedLinearIso 1 (P.embeddings i) (x i).1 = (x i).1
    rw [EmbeddedLinearGroup.embeddedLinearIso_one]
    rfl
  · change EmbeddedLinearGroup.embeddedLinearIso 1 (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) (x i).2 = (x i).2
    rw [EmbeddedLinearGroup.embeddedLinearIso_one]
    rfl

theorem Datum.RankThreePELDatum.referenceAmbientAction_mul (g h : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.referenceAmbientAction (g * h) = P.referenceAmbientAction g * P.referenceAmbientAction h := by
  apply LinearEquiv.ext
  intro x
  funext i
  apply Prod.ext
  · exact LinearEquiv.congr_fun (EmbeddedLinearGroup.embeddedLinearIso_mul (P.embeddings i) g h) (x i).1
  · exact LinearEquiv.congr_fun (EmbeddedLinearGroup.embeddedLinearIso_mul (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) g h) (x i).2

def Datum.RankThreePELDatum.referenceAmbientGroup : (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) →* (Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) where
  toFun g := P.referenceAmbientAction g
  map_one' := P.referenceAmbientAction_one
  map_mul' := P.referenceAmbientAction_mul

theorem Datum.RankThreePELDatum.referenceAmbientAction_inv_apply (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    P.referenceAmbientAction g⁻¹ (P.referenceAmbientAction g u) = u := by
  change (P.referenceAmbientGroup g⁻¹ * P.referenceAmbientGroup g) u = u
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem Datum.RankThreePELDatum.referenceAmbientAction_apply_inv (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    P.referenceAmbientAction g (P.referenceAmbientAction g⁻¹ u) = u := by
  change (P.referenceAmbientGroup g * P.referenceAmbientGroup g⁻¹) u = u
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
