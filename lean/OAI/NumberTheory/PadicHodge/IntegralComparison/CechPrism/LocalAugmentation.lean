import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSourceNaturality

/-! # Local Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalAugmentation

noncomputable section

/-! The genuine local diagonal cones give a natural map from the
frame diagram to its row Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex A ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def cone (V : Cᵒᵖ) : (Functor.const Cᵒᵖ).obj (Q.obj V) ⟶ B.obj V :=
  (Functor.const Cᵒᵖ).map ((γ.app V).app V) ≫
    GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C V.unop (B.obj V) (fun I => h I V.unop)

omit [HasProducts A] [HasCoproducts A] in
theorem cone_natural {V W : Cᵒᵖ} (f : V ⟶ W) :
    (Functor.const Cᵒᵖ).map (Q.map f) ≫ cone Q B γ h W =
      cone Q B γ h V ≫ B.map f := by
  apply NatTrans.ext
  funext I
  change Q.map f ≫ (DiagonalCone.rowMap Q B γ h I).app W =
    (DiagonalCone.rowMap Q B γ h I).app V ≫ (B.map f).app I
  exact (DiagonalCone.rowMap Q B γ h I).naturality f

def map : Q ⟶ B ⋙ GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U where
  app V := GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (B.obj V) (Q.obj V) (cone Q B γ h V)
  naturality V W f := by
    erw [GeometricComparison.CechCone.TotalSourceNaturality.CechConeTotalSourceNaturality.augmentation,
      GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.augmentation, cone_natural]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalAugmentation
