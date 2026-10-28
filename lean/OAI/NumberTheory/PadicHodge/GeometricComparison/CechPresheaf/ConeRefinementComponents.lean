import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinement

/-! # Cone Refinement Components -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents

noncomputable section

/-! Degreewise preservation of the original Cech cone edge under
actual projected refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ) (M : CochainComplex A ℕ)
  (η : (ConeTotal.CechPresheafConeTotal.constant (C := D)).obj M ⟶ K)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F

theorem augmentation (q : ℕ) : (ConeTotal.CechPresheafConeTotal.map V K M η).f q ≫ (RefinedReindex.CechPresheafRefinedReindex.map F U V r K).f q =
    (ConeTotal.CechPresheafConeTotal.map U (((H).mapHomologicalComplex (.up ℕ)).obj K) M (ConeRefinement.CechPresheafConeRefinement.cone F K M η)).f q :=
  congrArg (fun a => a.f q) (ConeRefinement.CechPresheafConeRefinement.augmentation F U V r K M η)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents
