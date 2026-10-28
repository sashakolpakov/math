import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Faces
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Global Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.GlobalAugmentation

noncomputable section

/-! The global-section augmentation in the native double Čech
complex, with its exact nonzero edge projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A] [HasFiniteCoproducts A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)

open OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic

local instance total : (IntrinsicComponents.Intrinsic.complex U B).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def cone : (Functor.const Cᵒᵖ).obj ((NonemptyCechNerve.complexFunctor U).obj Q) ⟶
    B ⋙ NonemptyCechNerve.complexFunctor U :=
  (Functor.constComp Cᵒᵖ Q (NonemptyCechNerve.complexFunctor U)).inv ≫
    Functor.whiskerRight γ (NonemptyCechNerve.complexFunctor U)

def map : ((NonemptyCechNerve.complexFunctor U).obj Q) ⟶
    GeometricComparison.CechCone.Total.CechConeTotal.total U (B ⋙ NonemptyCechNerve.complexFunctor U) :=
  GeometricComparison.CechCone.Total.CechConeTotal.augmentation U (B ⋙ NonemptyCechNerve.complexFunctor U)
    ((NonemptyCechNerve.complexFunctor U).obj Q) (cone U Q B γ)

omit [HasFiniteCoproducts A] [Finite ι] in
theorem component_projection (m : ℕ) (a : Fin (m + 1) → ι) (b : Fin 1 → ι) :
    GeometricComparison.CechCone.Total.CechConeTotal.component U (B ⋙ NonemptyCechNerve.complexFunctor U)
        ((NonemptyCechNerve.complexFunctor U).obj Q) (cone U Q B γ) m ≫
      IntrinsicComponents.Intrinsic.projection U B m 0 a b =
    NonemptyCechDifferential.projection U Q m a ≫
      (γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ a))) := by
  have hp := congrArg (fun f => f.f m)
    (Pi.lift_comp_π (fun b : Fin 1 → ι => (cone U Q B γ).app (op (∏ᶜ (U ∘ b)))) b)
  change _ ≫ _ = ((cone U Q B γ).app (op (∏ᶜ (U ∘ b)))).f m at hp
  change _ ≫ _ ≫ NonemptyCechDifferential.projection U (B.obj (op (∏ᶜ (U ∘ b)))) m a = _
  erw [← Category.assoc, hp]
  change (𝟙 _ ≫ (NonemptyCechNerve.complexFunctor U).map
    (γ.app (op (∏ᶜ (U ∘ b))))).f m ≫ _ = _
  erw [Category.id_comp]
  exact Pi.map_π (fun a : Fin (m + 1) → ι =>
    (γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ a)))) a

omit [Finite ι] in
theorem projection_self (m : ℕ) (a : Fin (m + 1) → ι) (b : Fin 1 → ι) :
    (GlobalAugmentation.map U Q B γ).f m ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) m 0 m ≫
        IntrinsicComponents.Intrinsic.projection U B m 0 a b =
      NonemptyCechDifferential.projection U Q m a ≫
        (γ.app (op (∏ᶜ (U ∘ b)))).app (op (∏ᶜ (U ∘ a))) := by
  change (_ ≫ (IntrinsicComponents.Intrinsic.complex U B).ιTotal (.up ℕ) m 0 m rfl) ≫ _ = _
  erw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_assoc]
  simp only [dite_true, HomologicalComplex₂.XXIsoOfEq, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact component_projection U Q B γ m a b

variable (h : ∀ I V : C, IsIso ((B.obj (op V)).map
  (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

omit [Finite ι] in
theorem value_self (m : ℕ) (a : Fin (m + 1) → ι) (b : Fin 1 → ι) :
    (GlobalAugmentation.map U Q B γ).f m ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) m 0 m ≫
        IntrinsicComponents.Intrinsic.projection U B m 0 a b =
      EvaluationNaturality.value U Q B γ h
        (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) m (List.ofFn a) := by
  rw [projection_self, SemilatticeCechAmalgamation.global_factorization Q B γ h]
  dsimp only [EvaluationNaturality.value]
  rw [Cech.LocalTupleEvaluation.value_ofFn U Q _ a inf_le_left, Category.assoc]

omit [Finite ι] in
theorem value_projection (N p q : ℕ) (hpq : p + q = N)
    (a : Fin (p + 1) → ι) (b : Fin (q + 1) → ι) :
    (GlobalAugmentation.map U Q B γ).f N ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (complex U B)) p q N ≫ IntrinsicComponents.Intrinsic.projection U B p q a b =
      if q = 0 then EvaluationNaturality.value U Q B γ h
        (∏ᶜ (U ∘ a)) (∏ᶜ (U ∘ b)) N (List.ofFn a) else 0 := by
  by_cases hq : q = 0
  · subst q
    have hN : N = p := by omega
    subst N
    exact value_self U Q B γ h p a b
  · rw [ite_eq_right hq]
    change (_ ≫ (IntrinsicComponents.Intrinsic.complex U B).ιTotal (.up ℕ) N 0 N rfl) ≫ _ = _
    erw [Category.assoc, AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_assoc]
    by_cases hp : N = p
    · simp only [dite_eq_left hp, dite_eq_right (Ne.symm hq), zero_comp]
      erw [comp_zero]
    · simp only [dite_eq_right hp, zero_comp]
      erw [comp_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.GlobalAugmentation
