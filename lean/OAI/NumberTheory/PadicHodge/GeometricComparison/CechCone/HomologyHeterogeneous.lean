import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HeterogeneousCongruence
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomologicalComponent

/-! # Homology Heterogeneous -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HomologyHeterogeneous.CechConeHomologyHeterogeneous

noncomputable section

/-! Object transport identifies the cohomology of cone edges without
first converting their total-complex components to homogeneous equality. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)
  (K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (M N : CochainComplex A ℕ)
  (η : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K)
  (θ : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj N ⟶ L)

omit [HasCoproducts.{0} A] in
theorem homology (hK : K = L) (hM : M = N) (hη : HEq η θ) (q : ℕ) :
    HEq (HomologicalComplex.homologyMap (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η) q)
      (HomologicalComplex.homologyMap (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ) q) := by
  cases hK
  cases hM
  have h : η = θ := eq_of_heq hη
  cases h
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.HomologyHeterogeneous.CechConeHomologyHeterogeneous
