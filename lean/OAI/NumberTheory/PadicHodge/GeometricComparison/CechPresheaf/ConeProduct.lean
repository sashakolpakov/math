import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinement

/-! # Cone Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct.CechPresheafConeProduct

noncomputable section

/-! Tuple-product reindexing preserves the original cone edge in
the presheaf Cech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

open OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal
universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ) (M : CochainComplex A ℕ)
  (η : (ConeTotal.CechPresheafConeTotal.constant (C := D)).obj M ⟶ K)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F
local notation "ηF" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F K M η
local notation "KF" => Functor.obj (Functor.mapHomologicalComplex H (ComplexShape.up ℕ)) K

omit [HasCoproducts.{0} A] in
theorem component_product (q : ℕ) : ConeTotal.CechPresheafConeTotal.component U KF M ηF q ≫
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).hom.f q).f 0 =
      ConeTotal.CechPresheafConeTotal.component (F.obj ∘ U) K M η q :=
  NonemptyCech.ProductAugmentation.NonemptyCechProductAugmentation.restriction F U (K.X q) (M.X q) (η.f q) ⦋0⦌

theorem augmentation : ConeTotal.CechPresheafConeTotal.map U KF M ηF ≫
    (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K) (.up ℕ)).hom =
      ConeTotal.CechPresheafConeTotal.map (F.obj ∘ U) K M η := by
  apply HomologicalComplex.Hom.ext
  funext q
  let B := ConeTotal.CechPresheafConeTotal.bicomplex U KF
  let D' := ConeTotal.CechPresheafConeTotal.bicomplex (F.obj ∘ U) K
  let a := (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).hom
  change (ConeTotal.CechPresheafConeTotal.component U KF M ηF q ≫ B.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    ConeTotal.CechPresheafConeTotal.component (F.obj ∘ U) K M η q ≫ D'.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => ConeTotal.CechPresheafConeTotal.component U KF M ηF q ≫ k)
      (HomologicalComplex₂.ιTotal_map B D' a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ D'.ιTotal (.up ℕ) q 0 q rfl)
            (component_product F U K M η q))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct.CechPresheafConeProduct
