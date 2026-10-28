import OAI.AlgebraicGeometry.PELModuli.CMPoints.Splitting

/-! # Common Embedded Fields -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonEmbeddedFields

noncomputable section

section

/-! Finitely many point fields over the arithmetic base embed in one
number field with their given base embeddings preserved. -/

theorem exists_complex_field_extension
    {B F : Type} [Field B] [NumberField B] [Field F] [NumberField F]
    (κ : B →+* ℂ) (i : B →+* F) :
    ∃ σ : F →+* ℂ, σ.comp i = κ := by
  let : Algebra B F := i.toAlgebra
  let : IsScalarTower ℚ B F := IsScalarTower.of_algebraMap_eq (fun r => by
    change (r : F) = i (r : B)
    simp)
  let : Algebra.IsAlgebraic B F := Algebra.IsAlgebraic.tower_top (K := ℚ) B
  let : Algebra B ℂ := κ.toAlgebra
  let σ : F →ₐ[B] ℂ := IsAlgClosed.lift
  exact ⟨σ.toRingHom, by ext x; exact σ.commutes x⟩

/-- The chosen common field is an actual finite subfield of C, and all
point-field maps agree on the prescribed arithmetic base. -/
theorem exists_compatible_common_field
    {B : Type} [Field B] [NumberField B] (κ : B →+* ℂ)
    {Idx : Type*} [Finite Idx] (F : Idx → Type)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)] (iF : ∀ i, B →+* F i) :
    ∃ C : Subfield ℂ, NumberField C ∧
      ∃ (iB : B →+* C) (eF : ∀ i, F i →+* C),
        C.subtype.comp iB = κ ∧ ∀ i, (eF i).comp (iF i) = iB := by
  classical
  choose σ hσ using (fun i => exists_complex_field_extension κ (iF i))
  let fields : Option Idx → Type
    | none => B
    | some i => F i
  let fieldStructures : ∀ i, Field (fields i)
    | none => inferInstanceAs (Field B)
    | some i => inferInstanceAs (Field (F i))
  let numberFields : ∀ i, NumberField (fields i)
    | none => inferInstanceAs (NumberField B)
    | some i => inferInstanceAs (NumberField (F i))
  let C := ComplexMultiplication.CommonCMField.CM.conjugateCompositum fields
  let iB := (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding fields none κ.toRatAlgHom).toRingHom
  let eF (i : Idx) :=
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding fields (some i) (σ i).toRatAlgHom).toRingHom
  refine ⟨C.toSubfield, inferInstanceAs (NumberField C), iB, eF, ?_, ?_⟩
  · rfl
  · intro i
    ext x
    exact RingHom.congr_fun (hσ i) x

end

/-! A common number field preserving every already chosen complex
embedding, including the individual CM model identifications. -/

theorem exists_common_embedded_numberField
    {I : Type*} [Finite I] (F : I → Type)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)] (κ : ∀ i, F i →+* ℂ) :
    ∃ C : Subfield ℂ, NumberField C ∧
      ∃ e : ∀ i, F i →+* C, ∀ i, C.subtype.comp (e i) = κ i := by
  let C := ComplexMultiplication.CommonCMField.CM.conjugateCompositum F
  let e (i : I) :=
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding F i (κ i).toRatAlgHom).toRingHom
  exact ⟨C.toSubfield, inferInstanceAs (NumberField C), e, fun _ => rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonEmbeddedFields
