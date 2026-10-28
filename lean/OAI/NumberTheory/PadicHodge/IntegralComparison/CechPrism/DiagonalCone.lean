import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents

/-! # Diagonal Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalCone

noncomputable section

/-! The actual local-cone augmentation of the coefficient diagonal,
composed with the given global-to-local coefficient transformation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

def diagonalMap : Q ⟶ GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.functor B where
  app V := (γ.app V).app V
  naturality V W f := by
    erw [GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal.map_eq, ← Category.assoc, ← (γ.app V).naturality f,
      Category.assoc]
    have hn := congrArg (fun a => a.app W) (γ.naturality f)
    change (𝟙 Q ≫ γ.app W).app W = (γ.app V ≫ B.map f).app W at hn
    change Q.map f ≫ (γ.app W).app W = Q.map f ≫ (γ.app V).app W ≫ (B.map f).app W
    simpa only [NatTrans.comp_app, NatTrans.id_app, Category.id_comp] using
      congrArg (fun a => Q.map f ≫ a) hn

def rowMap (I : Cᵒᵖ) : Q ⟶ B.flip.obj I :=
  diagonalMap Q B γ ≫
    GeometricComparison.Semilattice.DiagonalCone.SemilatticeDiagonalCone.component C B (fun V I => h I V) I

omit [Abelian A] [HasProducts A] in
theorem rowMap_app (I V : Cᵒᵖ) : (rowMap Q B γ h I).app V =
    (γ.app V).app V ≫
      (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C V.unop (B.obj V) (fun I => h I V.unop)).app I := rfl

def coefficient : Q ⟶
    (B ⋙ NonemptyCechNerve.complexFunctor U) ⋙ HomologicalComplex.eval A (.up ℕ) 0 where
  app V := Pi.lift (fun a : Fin 1 → ι => (rowMap Q B γ h (op (∏ᶜ (U ∘ a)))).app V)
  naturality V W f := by
    apply Pi.hom_ext
    intro (a : Fin 1 → ι)
    change (Q.map f ≫ _) ≫ Pi.π (fun a : Fin 1 → ι => (B.obj W).obj (op (∏ᶜ (U ∘ a)))) a = _
    erw [Category.assoc, Pi.lift_comp_π, Category.assoc]
    change _ = _ ≫ Limits.Pi.map (fun a : Fin 1 → ι => (B.map f).app (op (∏ᶜ (U ∘ a)))) ≫ _
    erw [Pi.map_π, Pi.lift_comp_π_assoc]
    exact (rowMap Q B γ h (op (∏ᶜ (U ∘ a)))).naturality f

omit [Finite ι] in
theorem coefficient_projection (V : Cᵒᵖ) (a : Fin 1 → ι) :
    (coefficient U Q B γ h).app V ≫
      NonemptyCechDifferential.projection U (B.obj V) 0 a =
    (γ.app V).app V ≫
      (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C V.unop (B.obj V) (fun I => h I V.unop)).app
        (op (∏ᶜ (U ∘ a))) := by
  exact Pi.lift_comp_π (fun a : Fin 1 → ι => (rowMap Q B γ h (op (∏ᶜ (U ∘ a)))).app V) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalCone
