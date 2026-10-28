import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafConeCoordinates

/-! # Cone Reference Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeReferenceQuasiIso.Reference

noncomputable section

/-! An original presheaf Čech edge detects quasi-isomorphisms in
the diagram presentation, including a genuine source coordinate isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  {M N : CochainComplex A ℕ} {K : CochainComplex (Cᵒᵖ ⥤ A) ℕ}
  (α : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ K)
  (β : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj N ⟶ K)
  (e : M ≅ N)
  (h : α = ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).map e.hom ≫ β)
  (hβ : QuasiIso (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K N β))

include h hβ in
theorem quasiIso : QuasiIso (ConeQuasiIso.map U α) := by
  have hb : QuasiIso (ConeQuasiIso.map U β) := by
    have heq := Cech.PresheafConeCoordinates.augmentation U K N β
    have ht : QuasiIso (ConeQuasiIso.map U β ≫
        (Cech.PresheafConeCoordinates.totalIso U K).hom) := heq.symm ▸ hβ
    exact (quasiIso_iff_comp_right _ (Cech.PresheafConeCoordinates.totalIso U K).hom).mp ht
  exact ConeQuasiIso.quasiIso U α β e (Iso.refl K)
    ((Category.comp_id α).trans h) hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeReferenceQuasiIso.Reference
