import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearPairing

/-! # Pairing Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PairingNaturality

noncomputable section

/-! Maps preserving actual presheaf pairings still preserve them after
the canonical sheafification and the underlying-section functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Functor.LaxMonoidal
open scoped TensorProduct

private theorem functor_pairing {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {M N P M' N' P' : C} (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P')
    (m : M ⊗ N ⟶ P) (m' : M' ⊗ N' ⟶ P')
    (h : (a ⊗ₘ b) ≫ m' = m ≫ c) :
    (F.map a ⊗ₘ F.map b) ≫ (μ F M' N' ≫ F.map m') =
      (μ F M N ≫ F.map m) ≫ F.map c := by
  rw [μ_natural_assoc, ← F.map_comp, h, F.map_comp, Category.assoc]

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

local notation "S" => presheafToSheaf J (ModuleCat R)
local notation "U" => sheafToPresheaf J (ModuleCat R)

local instance underlyingLax : (U).LaxMonoidal :=
  (sheafificationAdjunction J (ModuleCat R)).rightAdjointLaxMonoidal

variable {M N P M' N' P' : Cᵒᵖ ⥤ ModuleCat.{w} R}
  (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P')
  (m : M ⊗ N ⟶ P) (m' : M' ⊗ N' ⟶ P')
  (h : (a ⊗ₘ b) ≫ m' = m ≫ c)

include h in
theorem sheaf :
    ((S).map a ⊗ₘ (S).map b) ≫ TensorPairing.sheafPairing J R m' =
      TensorPairing.sheafPairing J R m ≫ (S).map c :=
  functor_pairing S a b c m m' h

include h in
theorem underlying :
    ((U).map ((S).map a) ⊗ₘ (U).map ((S).map b)) ≫
        TensorPairing.underlyingPairing J R m' =
      TensorPairing.underlyingPairing J R m ≫ (U).map ((S).map c) :=
  functor_pairing U ((S).map a) ((S).map b) ((S).map c)
    (TensorPairing.sheafPairing J R m)
    (TensorPairing.sheafPairing J R m') (sheaf J R a b c m m' h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PairingNaturality
