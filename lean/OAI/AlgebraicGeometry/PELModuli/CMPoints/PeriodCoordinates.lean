import OAI.AlgebraicGeometry.PELModuli.CMPoints.Products
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice

/-! # Period Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates

noncomputable section

section

/-! The diagonal reference period has three explicit rank-one CM
types. Their signs are determined by the changing line and the compact
places, and RiemannProjectivity realizes each type as an actual CM abelian variety. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def coordinateFirstSign (j : Fin 3) (i : Fin s) : Bool :=
  if i = P.distinguished then decide (j = 2) else !(P.compactSigns i)

def coordinateCMType (j : Fin 3) : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E := by
  let e := NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1
  refine ⟨fun σ => if (e.symm σ).2 then !(coordinateFirstSign P j (e.symm σ).1)
    else coordinateFirstSign P j (e.symm σ).1, ?_⟩
  intro σ
  obtain ⟨⟨i, b⟩, rfl⟩ := e.surjective σ
  rw [← NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs_conjugate]
  dsimp only [e]
  simp only [Equiv.symm_apply_apply]
  cases b <;> simp

theorem coordinateCMType_first (j : Fin 3) (i : Fin s) :
    (coordinateCMType P hP j).val (P.embeddings i) = coordinateFirstSign P j i := by
  have he : NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1 (i, false) = P.embeddings i := rfl
  change (if ((NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm (P.embeddings i)).2 then _ else _) = _
  rw [← he, Equiv.symm_apply_apply]
  rfl

theorem coordinateCMType_second (j : Fin 3) (i : Fin s) :
    (coordinateCMType P hP j).val (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) =
      !(coordinateFirstSign P j i) := by
  rw [(coordinateCMType P hP j).property, coordinateCMType_first]

def coordinateCMHodge : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E) :=
  Products.hodgePi (fun j => (coordinateCMType P hP j).hodgeStructure)

def coordinateCMDecomposition : ComplexMultiplication.Decomposition.CM.CMDecomposition (coordinateCMHodge P hP) :=
  Products.cmPiDecomposition E (fun j => (coordinateCMType P hP j).hodgeStructure)
    (fun j => (coordinateCMType P hP j).rankOneCMAction)

theorem coordinateCMRealization_hasCMH1 (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (coordinateCMHodge P hP)) :
    R.abelianVariety.HasCMH1 :=
  Products.realization_hasCMH1_of_product E (fun j => (coordinateCMType P hP j).hodgeStructure)
    (fun j => (coordinateCMType P hP j).rankOneCMAction) R

variable (F : IntermediateField ℚ ℂ) [NumberField F] [IsGalois ℚ F]
  [NumberField.IsCMField F]

def embeddingTypeToGaloisType (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType F) :
    ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(F/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation F * τ) :=
  ⟨fun τ => ε.val (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv F τ), fun τ => by
    change ε.val (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv F (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation F * τ)) =
      !(ε.val (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv F τ))
    exact (congrArg ε.val (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation F τ)).trans
      (ε.property _)⟩

theorem galoisType_recovers_embeddingType (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType F) :
    ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType F (embeddingTypeToGaloisType F ε) = ε := by
  apply Subtype.ext
  funext σ
  exact congrArg ε.val ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv F).apply_symm_apply σ)

theorem exists_CM_realization_of_embeddingType (hRiemannProjectivity : Realization.RiemannProjectivityInput)
    (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType F) :
    ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization ε.hodgeStructure, R.abelianVariety.HasCMH1 := by
  have h := Realization.exists_CM_realization hRiemannProjectivity F (embeddingTypeToGaloisType F ε)
  unfold ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure at h
  rw [galoisType_recovers_embeddingType] at h
  exact h

theorem exists_coordinate_CM_realizations (hRiemannProjectivity : Realization.RiemannProjectivityInput) (hCMAbelianVariety : Descent.AbelianInput)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum F s) (hP : P.IsAdmissible) :
    ∃ R : ∀ j : Fin 3, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (coordinateCMType P hP j).hodgeStructure,
      ∀ j, (R j).abelianVariety.HasCMH1 ∧ ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel (R j).abelianVariety := by
  have hex (j : Fin 3) := exists_CM_realization_of_embeddingType F hRiemannProjectivity (coordinateCMType P hP j)
  choose R hR using hex
  exact ⟨R, fun j => ⟨hR j, hCMAbelianVariety (R j).abelianVariety (hR j)⟩⟩

end

/-! The actual complexification of the three CM fields is identified
with the embedding coordinates of the rank-three PEL period domain. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem representativePairs_first (i : Fin s) :
    (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm (P.embeddings i) = (i, false) :=
  (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm_apply_apply (i, false)

theorem representativePairs_second (i : Fin s) :
    (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) = (i, true) :=
  (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm_apply_apply (i, true)

def pairedCoordinateEquiv : (Fin 3 → ((E →ₐ[ℚ] ℂ) → ℂ)) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) where
  toFun f i := (fun j => f j (P.embeddings i), fun j => f j (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)))
  invFun u j σ :=
    let p := (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).symm σ
    if p.2 then (u p.1).2 j else (u p.1).1 j
  left_inv f := by
    funext j σ
    obtain ⟨⟨i, b⟩, rfl⟩ := (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).surjective σ
    simp only [Equiv.symm_apply_apply]
    cases b <;> rfl
  right_inv u := by
    funext i
    apply Prod.ext <;> funext j
    · dsimp only
      rw [representativePairs_first P hP i]
      rfl
    · dsimp only
      rw [representativePairs_second P hP i]
      rfl
  map_add' f g := rfl
  map_smul' a f := rfl

def cmPeriodCoordinates : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E) ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s) :=
  Products.hodgePiCoordinates.trans ((LinearEquiv.piCongrRight
    (fun _ : Fin 3 => ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)).trans (pairedCoordinateEquiv P hP))

theorem cmPeriodCoordinates_first (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) (i : Fin s) (j : Fin 3) :
    (cmPeriodCoordinates P hP x i).1 j =
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (Products.hodgePiCoordinates x j) (P.embeddings i) := rfl

theorem cmPeriodCoordinates_second (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) (i : Fin s) (j : Fin 3) :
    (cmPeriodCoordinates P hP x i).2 j =
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (Products.hodgePiCoordinates x j) (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) := rfl

theorem cmPeriodCoordinates_conjugate (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    cmPeriodCoordinates P hP (ComplexMultiplication.WeightOne.CM.coefficientConjugation (Fin 3 → E) x) =
      Geometry.ComplexBall.PrescribedSignsB.realConj (cmPeriodCoordinates P hP x) := by
  funext i
  apply Prod.ext <;> funext j
  · change ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (Products.hodgePiCoordinates (ComplexMultiplication.WeightOne.CM.coefficientConjugation _ x) j)
      (P.embeddings i) = _
    rw [Products.hodgePiCoordinates_conjugate, ComplexMultiplication.CM.TypeHodgeStructure.fieldComplexificationEquiv_conjugation]
    rfl
  · change ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (Products.hodgePiCoordinates (ComplexMultiplication.WeightOne.CM.coefficientConjugation _ x) j)
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) = _
    rw [Products.hodgePiCoordinates_conjugate, ComplexMultiplication.CM.TypeHodgeStructure.fieldComplexificationEquiv_conjugation, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    rfl

def coordinateSignCondition (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) : Prop :=
  ∀ i j, ((u i).1 j ≠ 0 → coordinateFirstSign P j i = true) ∧
    ((u i).2 j ≠ 0 → (!(coordinateFirstSign P j i)) = true)

theorem coordinateCMHodge_holomorphic (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (coordinateCMHodge P hP).holomorphic ↔
      coordinateSignCondition P (cmPeriodCoordinates P hP x) := by
  change (∀ j, Products.hodgePiCoordinates x j ∈ (coordinateCMType P hP j).subspace true) ↔ _
  constructor
  · intro hx i j
    have h := ((coordinateCMType P hP j).mem_subspace_iff true _).mp (hx j)
    constructor
    · intro hn
      exact (coordinateCMType_first P hP j i).symm.trans (h (P.embeddings i) hn)
    · intro hn
      exact (coordinateCMType_second P hP j i).symm.trans (h (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) hn)
  · intro hx j
    apply ((coordinateCMType P hP j).mem_subspace_iff true _).mpr
    intro σ hn
    obtain ⟨⟨i, b⟩, rfl⟩ := (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).surjective σ
    cases b
    · exact (coordinateCMType_first P hP j i).trans ((hx i j).1 hn)
    · exact (coordinateCMType_second P hP j i).trans ((hx i j).2 hn)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates
