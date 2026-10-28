import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Heterogeneous Congruence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HeterogeneousCongruence.CechConeHeterogeneousCongruence

noncomputable section

/-! Transport an edge component by proved object equalities, keeping
its differently presented source and target types explicit. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)
  (K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (M N : CochainComplex A ℕ)
  (η : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K)
  (θ : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj N ⟶ L)

omit [HasCoproducts.{0} A] in
theorem component (hK : K = L) (hM : M = N) (hη : HEq η θ) (q : ℕ) :
    HEq ((CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η).f q) ((CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ).f q) := by
  cases hK
  cases hM
  have h : η = θ := eq_of_heq hη
  cases h
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HeterogeneousCongruence.CechConeHeterogeneousCongruence
