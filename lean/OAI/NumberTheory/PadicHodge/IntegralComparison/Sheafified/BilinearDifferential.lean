import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PairingNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.LaxPairing
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Bilinear Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearDifferential

noncomputable section

/-! The actual pointwise sheafified pairing satisfies every Leibniz
identity satisfied by the original presheaf pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Functor.LaxMonoidal
open scoped TensorProduct

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]
  [HasSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

local notation "S" => presheafToSheaf J (ModuleCat R)
local notation "U" => sheafToPresheaf J (ModuleCat R)

local instance underlyingLax : (U).LaxMonoidal :=
  (sheafificationAdjunction J (ModuleCat R)).rightAdjointLaxMonoidal

private theorem underlying_eq {M N P : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (m : M ⊗ N ⟶ P) : TensorPairing.underlyingPairing J R m =
      μ (S ⋙ U) M N ≫ (S ⋙ U).map m := by
  change μ U ((S).obj M) ((S).obj N) ≫ (U).map (μ S M N ≫ (S).map m) =
    (μ U ((S).obj M) ((S).obj N) ≫ (U).map (μ S M N)) ≫ (U).map ((S).map m)
  rw [(U).map_comp, Category.assoc]

variable (M N P M' N' P' : Cᵒᵖ ⥤ ModuleCat.{w} R)
  (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P')
  (μ₀ : ∀ V, M.obj V →ₗ[R] N.obj V →ₗ[R] P.obj V)
  (μ₁ : ∀ V, M'.obj V →ₗ[R] N.obj V →ₗ[R] P'.obj V)
  (μ₂ : ∀ V, M.obj V →ₗ[R] N'.obj V →ₗ[R] P'.obj V)
  (h₀ : ∀ {V W} (f : V ⟶ W) x y, P.map f (μ₀ V x y) = μ₀ W (M.map f x) (N.map f y))
  (h₁ : ∀ {V W} (f : V ⟶ W) x y, P'.map f (μ₁ V x y) = μ₁ W (M'.map f x) (N.map f y))
  (h₂ : ∀ {V W} (f : V ⟶ W) x y, P'.map f (μ₂ V x y) = μ₂ W (M.map f x) (N'.map f y))
  (z : ℤ) (hd : ∀ V x y, c.app V (μ₀ V x y) =
    μ₁ V (a.app V x) y + z • μ₂ V x (b.app V y))

include hd in
theorem differential (V : Cᵒᵖ) (x : ((S).obj M).obj.obj V) (y : ((S).obj N).obj.obj V) :
    (((S).map c).hom.app V) (BilinearPairing.pairing R M N P μ₀ h₀ J V x y) =
      BilinearPairing.pairing R M' N P' μ₁ h₁ J V (((S).map a).hom.app V x) y +
        z • BilinearPairing.pairing R M N' P' μ₂ h₂ J V x (((S).map b).hom.app V y) := by
  let m₀ := BilinearPairing.tensorPairing R M N P μ₀ h₀
  let m₁ := BilinearPairing.tensorPairing R M' N P' μ₁ h₁
  let m₂ := BilinearPairing.tensorPairing R M N' P' μ₂ h₂
  have hs : m₀ ≫ c = (a ⊗ₘ 𝟙 N) ≫ m₁ + z • ((𝟙 M ⊗ₘ b) ≫ m₂) := by
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro t
    exact hd W s t
  have h := Additive.LaxPairing.differential (S ⋙ U) a b c m₀ m₁ m₂ z hs
  rw [← underlying_eq J R m₀, ← underlying_eq J R m₁, ← underlying_eq J R m₂] at h
  have hv : _ = _ := NatTrans.congr_app h V
  exact congrArg (fun f : ((S).obj M).obj.obj V ⊗ ((S).obj N).obj.obj V ⟶
      ((S).obj P').obj.obj V => f (x ⊗ₜ[R] y)) hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearDifferential
