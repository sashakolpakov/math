import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyFiniteProducts

/-! # Tuple Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.TupleProducts

noncomputable section

/-! Tuples of actual frame maps are represented by the nonempty products of those frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (n : ℕ)

def family (t : Fin (n + 1) → ι) : C := ∏ᶜ (fun a => F (t a))

def equiv (U : C) :
    (Fin (n + 1) → ULift.{u} (Σ i, U ⟶ F i)) ≃
      ULift.{u} (Σ t, U ⟶ family F n t) where
  toFun x := ⟨⟨fun a => (x a).down.1, Pi.lift (fun a => (x a).down.2)⟩⟩
  invFun y := fun a => ⟨⟨y.down.1 a, y.down.2 ≫ Pi.π (fun b => F (y.down.1 b)) a⟩⟩
  left_inv x := by
    funext a
    apply ULift.ext
    refine Sigma.ext (by rfl) ?_
    exact heq_of_eq (Pi.lift_comp_π (fun a => (x a).down.2) a)
  right_inv y := by
    rcases y with ⟨⟨t, g⟩⟩
    apply ULift.ext
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Pi.hom_ext
    intro a
    exact Pi.lift_comp_π (fun b => g ≫ Pi.π (fun c => F (t c)) b) a

theorem equiv_natural {U V : C} (α : V ⟶ U)
    (x : Fin (n + 1) → ULift.{u} (Σ i, U ⟶ F i)) :
    equiv F n V (fun a => ⟨⟨(x a).down.1, α ≫ (x a).down.2⟩⟩) =
      (CoveringPresentationPresheaf.presentations (family F n)).map α.op (equiv F n U x) := by
  apply ULift.ext
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  change Pi.lift (fun a => α ≫ (x a).down.2) = α ≫ Pi.lift (fun a => (x a).down.2)
  apply Pi.hom_ext
  intro a
  simp only [Pi.lift_comp_π, Category.assoc]

def tuples : Cᵒᵖ ⥤ Type (max u v) where
  obj U := Fin (n + 1) → (CoveringPresentationPresheaf.presentations F).obj U
  map α := ↾fun x a => (CoveringPresentationPresheaf.presentations F).map α (x a)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    funext a
    exact congrArg (fun g => g (x a)) ((CoveringPresentationPresheaf.presentations F).map_id U)
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro x
    funext a
    exact congrArg (fun g => g (x a)) ((CoveringPresentationPresheaf.presentations F).map_comp α β)

def presheafIso : tuples F n ≅ CoveringPresentationPresheaf.presentations (family F n) :=
  NatIso.ofComponents (fun U => (equiv F n U.unop).toIso) (by
    intro U V α
    apply ConcreteCategory.hom_ext
    intro x
    exact equiv_natural F n α.unop x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.TupleProducts
