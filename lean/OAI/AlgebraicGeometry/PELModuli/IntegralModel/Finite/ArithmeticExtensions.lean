import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Arithmetic Extensions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Finitely many arithmetic extensions admit one common finite extension,
preserving every specified complex embedding exactly. -/

theorem Base.ArithmeticBaseExtension.finite_extensions_common
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    {I : Type} [Finite I] (D : I → Base.ArithmeticBaseExtension K κ)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, B.denominator = N ∧
      ∃ φ : ∀ i, (D i).extension.carrier →+* B.extension.carrier,
        (∀ i, (φ i).comp (algebraMap K (D i).extension.carrier) =
          algebraMap K B.extension.carrier) ∧
        (∀ i, B.embedding.comp (φ i) = (D i).embedding) := by
  let : Algebra K ℂ := κ.toAlgebra
  let a (i : I) : (D i).extension.carrier →ₐ[K] ℂ := {
    toRingHom := (D i).embedding
    commutes' := fun x => RingHom.congr_fun (D i).embedding_extends x }
  let L : IntermediateField K ℂ := ⨆ i, (a i).fieldRange
  have (i : I) : FiniteDimensional K (a i).fieldRange :=
    Module.Finite.equiv (a i).equivFieldRange.toLinearEquiv
  have : FiniteDimensional K L :=
    inferInstanceAs (FiniteDimensional K (⨆ i, (a i).fieldRange : IntermediateField K ℂ))
  have : NumberField L := NumberField.of_module_finite K L
  let B : Base.ArithmeticBaseExtension K κ := {
    extension := ⟨L⟩
    embedding := L.val.toRingHom
    embedding_extends := by ext x; rfl
    denominator := N
    denominator_ne_zero := hN }
  let φ (i : I) : (D i).extension.carrier →ₐ[K] L :=
    (IntermediateField.inclusion (le_iSup (fun i => (a i).fieldRange) i)).comp
      (a i).equivFieldRange.toAlgHom
  refine ⟨B, rfl, (fun i => (φ i).toRingHom), ?_, ?_⟩
  · intro i
    apply RingHom.ext
    intro x
    exact (φ i).commutes x
  · intro i
    ext x
    rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
