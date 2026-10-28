import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.TensorPairing

/-! # Bilinear Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearPairing

noncomputable section

/-! Pointwise bilinear pairings after genuine module sheafification,
normalized by the actual sheafification unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M N P : Cᵒᵖ ⥤ ModuleCat.{w} R)
  (μ : ∀ U, M.obj U →ₗ[R] N.obj U →ₗ[R] P.obj U)
  (hμ : ∀ {U V} (f : U ⟶ V) x y,
    P.map f (μ U x y) = μ V (M.map f x) (N.map f y))

def tensorPairing : M ⊗ N ⟶ P where
  app U := ModuleCat.ofHom (TensorProduct.lift (μ U))
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (hμ f x y).symm

variable (J : GrothendieckTopology C)
  [HasWeakSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

local notation "S" => presheafToSheaf J (ModuleCat R)
local notation "adj" => sheafificationAdjunction J (ModuleCat R)

def pairing (U : Cᵒᵖ) : ((S).obj M).obj.obj U →ₗ[R]
    ((S).obj N).obj.obj U →ₗ[R] ((S).obj P).obj.obj U :=
  TensorProduct.curry ((TensorPairing.underlyingPairing J R
    (tensorPairing R M N P μ hμ)).app U).hom

theorem unit_pairing (U : Cᵒᵖ) (x : M.obj U) (y : N.obj U) :
    ((adj).unit.app P).app U (μ U x y) =
      pairing R M N P μ hμ J U
        (((adj).unit.app M).app U x) (((adj).unit.app N).app U y) := by
  have h := congrArg (fun a => a.app U)
    (TensorPairing.unit_pairing J R (tensorPairing R M N P μ hμ))
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) (x ⊗ₜ[R] y)).symm

theorem pairing_natural {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((S).obj M).obj.obj U) (y : ((S).obj N).obj.obj U) :
    ((S).obj P).obj.map f (pairing R M N P μ hμ J U x y) =
      pairing R M N P μ hμ J V (((S).obj M).obj.map f x) (((S).obj N).obj.map f y) := by
  have h := (TensorPairing.underlyingPairing J R
    (tensorPairing R M N P μ hμ)).naturality f
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) (x ⊗ₜ[R] y)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearPairing
