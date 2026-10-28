import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramNaturality

/-! # Diagram Complex Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap

noncomputable section

/-!
# IntegralComparison: morphisms of original crystalline diagrams preserve the augmented relative complexes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

def map : RelativeCrystalline.ModuleComplex.complex K Q ρ ⟶
    RelativeCrystalline.ModuleComplex.complex H Q π where
  f n := DiagramNaturality.presheafMap H K Q π ρ θ hθ n
  comm' n m h := by
    change n + 1 = m at h
    subst m
    rw [RelativeCrystalline.ModuleComplex.complex_d, RelativeCrystalline.ModuleComplex.complex_d]
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (DiagramFormMap.map_differential H K Q π ρ θ hθ U.unop n ω).symm

theorem constants (U : C) (a : (Q.obj U).ring) :
    DiagramFormMap.map H K Q π ρ θ hθ U 0
      (RelativeCrystalline.Augmentation.constants K Q ρ U a) =
        RelativeCrystalline.Augmentation.constants H Q π U a := by
  rw [RelativeCrystalline.Augmentation.constants_symbol, DiagramFormMap.map_symbol,
    RelativeCrystalline.Augmentation.constants_symbol]
  apply congrArg₂ (RelativeCrystalline.FormData.symbol H Q π U 0)
  · exact congrArg (fun τ : H ⟶ Q => (τ.app U).ringMap a) hθ
  · funext i
    exact i.elim0

theorem augmentationZero : RelativeCrystalline.ModuleComplex.augmentationZero K Q ρ ≫
    DiagramNaturality.presheafMap H K Q π ρ θ hθ 0 =
      RelativeCrystalline.ModuleComplex.augmentationZero H Q π := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact constants H K Q π ρ θ hθ U.unop a

theorem augmentation : RelativeCrystalline.ModuleComplex.augmentation K Q ρ ≫ map H K Q π ρ θ hθ =
    RelativeCrystalline.ModuleComplex.augmentation H Q π := by
  apply (CochainComplex.fromSingle₀Equiv (RelativeCrystalline.ModuleComplex.complex H Q π)
    (RelativeCrystalline.ModuleComplex.ambientPresheaf Q)).injective
  apply Subtype.ext
  change (RelativeCrystalline.ModuleComplex.augmentation K Q ρ).f 0 ≫
      DiagramNaturality.presheafMap H K Q π ρ θ hθ 0 =
    (RelativeCrystalline.ModuleComplex.augmentation H Q π).f 0
  rw [RelativeCrystalline.ModuleComplex.augmentation_zero,
    RelativeCrystalline.ModuleComplex.augmentation_zero]
  exact augmentationZero H K Q π ρ θ hθ

theorem quasiIso [QuasiIso (RelativeCrystalline.ModuleComplex.augmentation K Q ρ)]
    [QuasiIso (RelativeCrystalline.ModuleComplex.augmentation H Q π)] : QuasiIso (map H K Q π ρ θ hθ) := by
  have : QuasiIso (RelativeCrystalline.ModuleComplex.augmentation K Q ρ ≫ map H K Q π ρ θ hθ) := by
    rw [augmentation]
    infer_instance
  exact quasiIso_of_comp_left
    (RelativeCrystalline.ModuleComplex.augmentation K Q ρ) (map H K Q π ρ θ hθ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap
