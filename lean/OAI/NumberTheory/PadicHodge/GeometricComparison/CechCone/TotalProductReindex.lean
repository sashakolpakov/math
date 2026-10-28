import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor

/-! # Total Product Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindex.CechConeTotalProductReindex

noncomputable section

/-! Reindexing the covering family through a functor preserving its
tuple products commutes with original Cech totalization and augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe v vD vA u uD uA
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι : Type} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

local instance hasTotal (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def bicomplexIso : Total.CechConeTotal.bicomplex U (F.op ⋙ P) ≅ Total.CechConeTotal.bicomplex (F.obj ∘ U) P :=
  (HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).mapIso
    (NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P)

def iso : Total.CechConeTotal.total U (F.op ⋙ P) ≅ Total.CechConeTotal.total (F.obj ∘ U) P :=
  (HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)).mapIso (bicomplexIso F U P)

variable (M : CochainComplex A ℕ) (η : (Functor.const Dᵒᵖ).obj M ⟶ P)

theorem augmentation :
    Total.CechConeTotal.augmentation U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) ≫ (iso F U P).hom =
      Total.CechConeTotal.augmentation (F.obj ∘ U) P M η := by
  ext q : 1
  let K := Total.CechConeTotal.bicomplex U (F.op ⋙ P)
  let L := Total.CechConeTotal.bicomplex (F.obj ∘ U) P
  let a := (bicomplexIso F U P).hom
  have hq := congrArg (fun f => f.f q) (NonemptyCech.ProductAugmentation.NonemptyCechProductAugmentation.restriction F U P M η ⦋0⦌)
  change Total.CechConeTotal.component U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) q ≫ (a.f q).f 0 =
    Total.CechConeTotal.component (F.obj ∘ U) P M η q at hq
  change (Total.CechConeTotal.component U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) q ≫ K.ιTotal (.up ℕ) q 0 q rfl) ≫
      (HomologicalComplex₂.total.map a (.up ℕ)).f q =
    Total.CechConeTotal.component (F.obj ∘ U) P M η q ≫ L.ιTotal (.up ℕ) q 0 q rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Total.CechConeTotal.component U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) q ≫ k)
      (HomologicalComplex₂.ιTotal_map K L a (.up ℕ) q 0 q rfl)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ L.ιTotal (.up ℕ) q 0 q rfl) hq)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindex.CechConeTotalProductReindex
