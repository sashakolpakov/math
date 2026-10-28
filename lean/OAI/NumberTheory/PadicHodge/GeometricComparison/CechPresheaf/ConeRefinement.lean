import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductAugmentation

/-! # Cone Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement

noncomputable section

/-! Projected refinement preserves the canonical cone edge into the
original presheaf Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

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

def cone : (ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ ((H).mapHomologicalComplex (.up ℕ)).obj K :=
  ((H).mapHomologicalComplex (.up ℕ)).map η

omit [HasCoproducts.{0} A] in
theorem cochains (q : ℕ) : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation V (K.X q) (M.X q) (η.f q) ≫
    (RefinedReindex.CechPresheafRefinedReindex.transformation F U V r).app (K.X q) =
      NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U (F.op ⋙ K.X q) (M.X q) (Functor.whiskerLeft F.op (η.f q)) := by
  let e := NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (K.X q)
  apply (cancel_mono e.hom).1
  change (NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation V (K.X q) (M.X q) (η.f q) ≫
      (NonemptyCech.Refinement.NonemptyCechRefinement.map V (F.obj ∘ U) r (K.X q) ≫ e.inv)) ≫ e.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (NonemptyCech.Refinement.NonemptyCechRefinement.augmentation V (F.obj ∘ U) r (K.X q) (M.X q) (η.f q)).trans
    (NonemptyCech.ProductAugmentation.NonemptyCechProductAugmentation.augmentation F U (K.X q) (M.X q) (η.f q)).symm

omit [HasCoproducts.{0} A] in
theorem component_refinement (q : ℕ) : ConeTotal.CechPresheafConeTotal.component V K M η q ≫
    ((RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K).f q).f 0 =
      ConeTotal.CechPresheafConeTotal.component U (((H).mapHomologicalComplex (.up ℕ)).obj K) M (cone F K M η) q := by
  have h := congrArg (fun f => f.f 0) (cochains F U V r K M η q)
  have hl := NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero V (K.X q) (M.X q) (η.f q)
  have hr := NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation_zero U (F.op ⋙ K.X q) (M.X q)
    (Functor.whiskerLeft F.op (η.f q))
  exact (congrArg (fun a => a ≫ ((RefinedReindex.CechPresheafRefinedReindex.transformation F U V r).app (K.X q)).f 0)
    hl.symm).trans (h.trans hr)

theorem augmentation : ConeTotal.CechPresheafConeTotal.map V K M η ≫ RefinedReindex.CechPresheafRefinedReindex.map F U V r K =
    ConeTotal.CechPresheafConeTotal.map U (((H).mapHomologicalComplex (.up ℕ)).obj K) M (cone F K M η) := by
  apply HomologicalComplex.Hom.ext
  funext q
  let B := ConeTotal.CechPresheafConeTotal.bicomplex V K
  let D' := ConeTotal.CechPresheafConeTotal.bicomplex U (((H).mapHomologicalComplex (.up ℕ)).obj K)
  let a := RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K
  change (ConeTotal.CechPresheafConeTotal.component V K M η q ≫ B.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    ConeTotal.CechPresheafConeTotal.component U (((H).mapHomologicalComplex (.up ℕ)).obj K) M (cone F K M η) q ≫
      D'.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => ConeTotal.CechPresheafConeTotal.component V K M η q ≫ k)
      (HomologicalComplex₂.ιTotal_map B D' a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ D'.ιTotal (.up ℕ) q 0 q rfl)
            (component_refinement F U V r K M η q))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement
