import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal

/-! # Cone Component Congr -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr

noncomputable section

/-! The degree-q Cech edge only depends on the degree-q cone components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
universe u v a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} (U : ι → C)
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ) (M : CochainComplex A ℕ)
  (η θ : (ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K) (q : ℕ)
  (h : ∀ V, (η.f q).app V = (θ.f q).app V)

include h in
theorem component : (ConeTotal.CechPresheafConeTotal.map U K M η).f q = (ConeTotal.CechPresheafConeTotal.map U K M θ).f q :=
  congrArg (fun α => (NonemptyCech.Augmentation.NonemptyCechAugmentation.restriction U (K.X q) (M.X q) α).app ⦋0⦌ ≫
    (ConeTotal.CechPresheafConeTotal.bicomplex U K).ιTotal (.up ℕ) q 0 q rfl) (NatTrans.ext (funext h))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr
