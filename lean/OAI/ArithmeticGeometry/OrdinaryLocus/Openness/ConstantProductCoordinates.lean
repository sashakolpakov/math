import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Constant Product Coordinates -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCoordinates.Construction

noncomputable section

/-! The product of two constant families as an actual scheme over the original field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

universe u

variable {K : Type u} [Field K] (A B S : Over (Spec (.of K)))

abbrev constantLeftBase : (A ⊗ S).left ⟶ S.left := (snd A S).left
abbrev constantRightBase : (B ⊗ S).left ⟶ S.left := (snd B S).left

abbrev constantProductProjection : pullback (constantLeftBase A S) (constantRightBase B S) ⟶ S.left :=
  pullback.fst (constantLeftBase A S) (constantRightBase B S) ≫ constantLeftBase A S

abbrev constantProduct : Over (Spec (.of K)) := Over.mk (constantProductProjection A B S ≫ S.hom)

def constantProductLeft : constantProduct A B S ⟶ A ⊗ S :=
  Over.homMk (pullback.fst (constantLeftBase A S) (constantRightBase B S)) (by
    rw [← Over.w (snd A S)]
    exact (Category.assoc _ _ _).symm)

def constantProductRight : constantProduct A B S ⟶ B ⊗ S :=
  Over.homMk (pullback.snd (constantLeftBase A S) (constantRightBase B S)) (by
    rw [← Over.w (snd B S), ← Category.assoc, ← pullback.condition]
    rfl)

def constantProductBase : constantProduct A B S ⟶ S :=
  Over.homMk (constantProductProjection A B S)

theorem constantProductLeft_base : constantProductLeft A B S ≫ snd A S = constantProductBase A B S := by
  ext1
  rfl

theorem constantProductRight_base : constantProductRight A B S ≫ snd B S = constantProductBase A B S := by
  ext1
  exact pullback.condition.symm

def constantFamilySection (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) : S ⟶ A ⊗ S :=
  lift (toUnit S ≫ sA) (𝟙 S)

theorem constantFamilySection_base (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    constantFamilySection A S sA ≫ snd A S = 𝟙 S := lift_snd _ _

theorem constantFamilySection_factor (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    constantFamilySection A S sA ≫ fst A S = toUnit S ≫ sA := lift_fst _ _

def constantProductLeftAxis (sB : 𝟙_ (Over (Spec (.of K))) ⟶ B) : A ⊗ S ⟶ constantProduct A B S :=
  Over.homMk (OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left (constantLeftBase A S) (constantRightBase B S)
    (constantFamilySection B S sB).left (congrArg Over.Hom.left (constantFamilySection_base B S sB))) (by
      have h := OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.left_over (constantLeftBase A S) (constantRightBase B S)
        (constantFamilySection B S sB).left (congrArg Over.Hom.left (constantFamilySection_base B S sB))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m : (A ⊗ S).left ⟶ S.left ↦ m ≫ S.hom) h).trans (Over.w (snd A S))))

def constantProductRightAxis (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) : B ⊗ S ⟶ constantProduct A B S :=
  Over.homMk (OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right (constantLeftBase A S) (constantRightBase B S)
    (constantFamilySection A S sA).left (congrArg Over.Hom.left (constantFamilySection_base A S sA))) (by
      have h := OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes.right_over (constantLeftBase A S) (constantRightBase B S)
        (constantFamilySection A S sA).left (congrArg Over.Hom.left (constantFamilySection_base A S sA))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m : (B ⊗ S).left ⟶ S.left ↦ m ≫ S.hom) h).trans (Over.w (snd B S))))

theorem constantProductLeftAxis_left (sB : 𝟙_ (Over (Spec (.of K))) ⟶ B) :
    constantProductLeftAxis A B S sB ≫ constantProductLeft A B S = 𝟙 (A ⊗ S) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst (f := constantLeftBase A S) (g := constantRightBase B S) _ _ _

theorem constantProductLeftAxis_right (sB : 𝟙_ (Over (Spec (.of K))) ⟶ B) :
    constantProductLeftAxis A B S sB ≫ constantProductRight A B S = snd A S ≫ constantFamilySection B S sB := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd (f := constantLeftBase A S) (g := constantRightBase B S) _ _ _

theorem constantProductRightAxis_left (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    constantProductRightAxis A B S sA ≫ constantProductLeft A B S = snd B S ≫ constantFamilySection A S sA := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst (f := constantLeftBase A S) (g := constantRightBase B S) _ _ _

theorem constantProductRightAxis_right (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    constantProductRightAxis A B S sA ≫ constantProductRight A B S = 𝟙 (B ⊗ S) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd (f := constantLeftBase A S) (g := constantRightBase B S) _ _ _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCoordinates.Construction
