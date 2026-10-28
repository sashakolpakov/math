import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents

/-! # Differentials -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Differentials

noncomputable section

/-! Both differentials of the literal double Čech complex in their
native product projections. These are the faces used by the signed prism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic

omit [Finite ι] in
theorem inner (m n : ℕ) (a : Fin (m + 2) → ι) (b : Fin (n + 1) → ι) :
    ((IntrinsicComponents.Intrinsic.complex U B).d m (m + 1)).f n ≫ IntrinsicComponents.Intrinsic.projection U B (m + 1) n a b =
      ∑ i : Fin (m + 2), (-1 : ℤ)^i.val •
        (IntrinsicComponents.Intrinsic.projection U B m n (a ∘ i.succAbove) b ≫
          (B.obj (op (∏ᶜ (U ∘ b)))).map
            (NonemptyCechDifferential.faceMap U m i a).op) := by
  let πb := Pi.π (fun b : Fin (n + 1) → ι =>
    (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b))))) b
  change (∏ᶜ (fun b : Fin (n + 1) → ι =>
    (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b)))))).d m (m + 1) ≫ πb.f (m + 1) ≫ NonemptyCechDifferential.projection U
    (B.obj (op (∏ᶜ (U ∘ b)))) (m + 1) a = _
  erw [← Category.assoc, ← πb.comm, Category.assoc,
    NonemptyCechDifferential.differential_projection, comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_zsmul, ← Category.assoc]
  rfl

omit [Finite ι] in
theorem outer (m n : ℕ) (a : Fin (m + 1) → ι) (b : Fin (n + 2) → ι) :
    ((IntrinsicComponents.Intrinsic.complex U B).X m).d n (n + 1) ≫ IntrinsicComponents.Intrinsic.projection U B m (n + 1) a b =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
        (IntrinsicComponents.Intrinsic.projection U B m n a (b ∘ i.succAbove) ≫
          (B.map (NonemptyCechDifferential.faceMap U n i b).op).app
            (op (∏ᶜ (U ∘ a)))) := by
  have h := congrArg (HomologicalComplex.eval A (.up ℕ) m).map
    (NonemptyCechDifferential.differential_projection U
      (B ⋙ NonemptyCechNerve.complexFunctor U) n b)
  simp only [Functor.map_comp, Functor.map_sum, Functor.map_zsmul] at h
  have hp := congrArg (fun f => f ≫ NonemptyCechDifferential.projection U
    (B.obj (op (∏ᶜ (U ∘ b)))) m a) h
  dsimp only [HomologicalComplex.eval] at hp
  simp only [Category.assoc] at hp
  refine hp.trans ?_
  erw [sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  erw [zsmul_comp]
  congr 1
  erw [Category.assoc]
  change _ ≫ (Limits.Pi.map (fun c : Fin (m + 1) → ι =>
    (B.map (NonemptyCechDifferential.faceMap U n i b).op).app (op (∏ᶜ (U ∘ c))))) ≫
      NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) m a = _
  erw [Pi.map_π, ← Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Differentials
