import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticExtensions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Specialization

/-! # Arithmetic Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticPoints

noncomputable section

/-! Finitely many nonempty finite-type parameter schemes have points over
one finite number-field extension with the prescribed complex embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finite_arithmetic_parameters_exist
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {I : Type} [Finite I] (X : I → Over (Spec (.of K)))
    [∀ i, LocallyOfFiniteType (X i).hom] [∀ i, Nonempty (X i).left]
    (N : ℕ) (hN : N ≠ 0) :
    ∃ B : Base.ArithmeticBaseExtension K κ, B.denominator = N ∧
      Nonempty (∀ i, Over.mk B.fieldExtension ⟶ X i) := by
  have hx (i : I) := Arithmetic.Specialization.arithmetic_parameter_exists κ (X i) N hN
  choose D p _ using hx
  obtain ⟨B, hB, φ, hφ, _⟩ := Base.ArithmeticBaseExtension.finite_extensions_common D N hN
  let q (i : I) : Over.mk B.fieldExtension ⟶ Over.mk (D i).fieldExtension :=
    Over.homMk (Spec.map (CommRingCat.ofHom (φ i))) (by
      change Spec.map (CommRingCat.ofHom (φ i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (D i).extension.carrier)) =
          Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier))
      rw [← Spec.map_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (hφ i))
  exact ⟨B, hB, ⟨fun i => q i ≫ p i⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ArithmeticPoints
