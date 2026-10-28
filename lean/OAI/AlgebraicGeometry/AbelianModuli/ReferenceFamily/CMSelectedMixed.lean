import OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMMixedHermitianForm

/-! # CM Selected Mixed -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed

noncomputable section

section

/-! The direct CM mixed realization has actual coordinates at the
original selected embeddings. The real equivalence agrees exactly
with those original embeddings on every rational CM vector. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

open OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

def cmSelectedMixedCoordinates :
    (Fin 3 → mixedSpace E) ≃ₗ[ℝ] (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :=
  (LinearEquiv.piCongrRight (fun _ : Fin 3 => (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ).mixedPeriodEquiv)).trans
    ((NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.periodCoordinateEquiv σ hσ).restrictScalars ℝ)

omit [Fintype Place] in
theorem cmSelectedMixedCoordinates_embedding (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    cmSelectedMixedCoordinates σ hσ (fun j => mixedEmbedding E (v j)) =
      fun p j => σ p (v j) := by
  change NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.periodCoordinateEquiv σ hσ
    (fun j => (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ).mixedPeriodEquiv (mixedEmbedding E (v j))) = _
  simp_rw [ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mixedPeriodEquiv_mixedEmbedding]
  exact NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.periodCoordinateEquiv_embedding σ hσ v

end

section

/-! The same original selected-place coordinates identify the
mixed coefficient algebra with the product of complex fields, as a
real algebra and compatibly with complex conjugation. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

open OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel

variable {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

omit [NumberField E] [IsCMField E] in
theorem selected_periodConjugation_mul (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (p : InfinitePlace E) (z w : ℂ) :
    ε.periodConjugation p (z * w) = ε.periodConjugation p z * ε.periodConjugation p w := by
  unfold ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.periodConjugation
  split_ifs <;> simp

omit [NumberField E] [IsCMField E] in
theorem selected_periodConjugation_one (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (p : InfinitePlace E) :
    ε.periodConjugation p 1 = 1 := by
  unfold ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.periodConjugation
  split_ifs <;> simp

omit [NumberField E] [IsCMField E] in
theorem selected_periodConjugation_star (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (p : InfinitePlace E) (z : ℂ) :
    ε.periodConjugation p (star z) = star (ε.periodConjugation p z) := by
  unfold ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.periodConjugation
  split_ifs <;> simp

def selectedPeriodScalarReindex : ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E ≃ₗ[ℝ] (Place → ℂ) where
  toFun x p := x (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p)
  invFun x p := x ((NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ).symm p)
  left_inv x := by ext p; simp
  right_inv x := by ext p; simp
  map_add' x y := rfl
  map_smul' a x := rfl

def cmSelectedMixedScalarRealEquiv : mixedSpace E ≃ₗ[ℝ] (Place → ℂ) :=
  (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ).mixedPeriodEquiv.trans (selectedPeriodScalarReindex σ hσ)

def cmSelectedMixedScalarAlgebraEquiv : mixedSpace E ≃ₐ[ℝ] (Place → ℂ) where
  toEquiv := (cmSelectedMixedScalarRealEquiv σ hσ).toEquiv
  map_add' := (cmSelectedMixedScalarRealEquiv σ hσ).map_add
  map_mul' x y := by
    ext p
    exact selected_periodConjugation_mul (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ) (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p) _ _
  commutes' a := by
    have h1 : cmSelectedMixedScalarRealEquiv σ hσ 1 = 1 := by
      ext p
      exact selected_periodConjugation_one (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ) (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p)
    change cmSelectedMixedScalarRealEquiv σ hσ (algebraMap ℝ (mixedSpace E) a) =
      algebraMap ℝ (Place → ℂ) a
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, ← Algebra.algebraMap_eq_smul_one]

omit [Fintype Place] in
theorem cmSelectedMixedScalarAlgebraEquiv_star (x : mixedSpace E) :
    cmSelectedMixedScalarAlgebraEquiv σ hσ (star x) =
      star (cmSelectedMixedScalarAlgebraEquiv σ hσ x) := by
  ext p
  exact selected_periodConjugation_star (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ) (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p) _

omit [Fintype Place] in
theorem cmSelectedMixedScalarAlgebraEquiv_embedding (a : E) (p : Place) :
    cmSelectedMixedScalarAlgebraEquiv σ hσ (mixedEmbedding E a) p = σ p a := by
  change (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ).mixedPeriodEquiv (mixedEmbedding E a)
    (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p) = σ p a
  rw [ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mixedPeriodEquiv_mixedEmbedding]
  change (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.referenceCMType σ hσ).placeEmbedding (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePlaces σ hσ p) a = _
  rw [NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.placeEmbedding_representative]

omit [Fintype Place] in
theorem cmSelectedMixedCoordinates_apply (x : Fin 3 → mixedSpace E) (p : Place) (i : Fin 3) :
    cmSelectedMixedCoordinates σ hσ x p i = cmSelectedMixedScalarAlgebraEquiv σ hσ (x i) p := rfl

end

/-! The actual mixed Hermitian form is exactly the tuple of native
Hermitian forms at the original selected embeddings. Thus an actual
intertwining with component maps preserves precisely those forms. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

open OAI.NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel

variable {E : Type} {Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [IsCMField E] [Fintype Place]
  (σ : Place → E →ₐ[ℚ] ℂ)
  (hσ : Function.Bijective
    (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))

local notation "V" => Fin 3 → mixedSpace E
local notation "Φ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedCoordinates σ hσ
local notation "e" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed.cmSelectedMixedScalarAlgebraEquiv σ hσ

omit [Fintype Place] in
theorem cmSelectedMixedHermitian_value
    (H : Matrix (Fin 3) (Fin 3) E) (x y : V) (p : Place) :
    e (CMMixedHermitianForm.cmMixedHermitianForm H x y) p =
      Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H (Φ x p) (Φ y p) := by
  simp only [CMMixedHermitianForm.cmMixedHermitianForm_apply, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply,
    cmSelectedMixedScalarAlgebraEquiv_star, Pi.star_apply,
    cmSelectedMixedScalarAlgebraEquiv_embedding, Datum.RankThreePELDatum.complexMatrixHermitian,
    cmSelectedMixedCoordinates_apply]
  rfl

omit [Fintype Place] in
theorem cmSelectedMixedHermitian_isometry_iff
    (H : Matrix (Fin 3) (Fin 3) E)
    (f : V ≃ₗ[ℝ] V) (q : Place → Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hq : ∀ x p, Φ (f x) p = q p (Φ x p)) :
    (∀ x y, CMMixedHermitianForm.cmMixedHermitianForm H (f x) (f y) = CMMixedHermitianForm.cmMixedHermitianForm H x y) ↔
      ∀ p x y, Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H (q p x) (q p y) =
        Datum.RankThreePELDatum.complexMatrixHermitian (σ p).toRingHom H x y := by
  constructor
  · intro hf p x y
    let v := (Φ).symm (fun _ => x)
    let w := (Φ).symm (fun _ => y)
    have hv : Φ v p = x := congrFun ((Φ).apply_symm_apply (fun _ => x)) p
    have hw : Φ w p = y := congrFun ((Φ).apply_symm_apply (fun _ => y)) p
    have he := congrArg (fun a => e a p) (hf v w)
    rw [cmSelectedMixedHermitian_value, cmSelectedMixedHermitian_value, hq, hq, hv, hw] at he
    exact he
  · intro h x y
    apply (e).injective
    ext p
    rw [cmSelectedMixedHermitian_value, cmSelectedMixedHermitian_value, hq, hq]
    exact h p (Φ x p) (Φ y p)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMSelectedMixed
