import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! # Tensor Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.TensorPairing

noncomputable section

/-! The actual sheafification unit preserves the pairing obtained by
sheafifying a presheaf tensor pairing. This records the normalization
needed by the native crystalline coefficient augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

private theorem adjunction_pairing {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C}
    (adj : F ⊣ G) [G.LaxMonoidal] [adj.IsMonoidal]
    {M N P : C} (m : M ⊗ N ⟶ P) :
    (adj.unit.app M ⊗ₘ adj.unit.app N) ≫ μ G (F.obj M) (F.obj N) ≫
        G.map (μ F M N ≫ F.map m) = m ≫ adj.unit.app P := by
  rw [← Category.assoc, ← adj.unit_app_tensor_comp_map_δ,
    Category.assoc, G.map_comp, ← Category.assoc (G.map (δ F M N)),
    map_δ_μ, Category.id_comp]
  exact (adj.unit.naturality m).symm

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

local notation "S" => presheafToSheaf J (ModuleCat R)
local notation "U" => sheafToPresheaf J (ModuleCat R)
local notation "adj" => sheafificationAdjunction J (ModuleCat R)

local instance underlyingLax : (U).LaxMonoidal := (adj).rightAdjointLaxMonoidal

variable {M N P : Cᵒᵖ ⥤ ModuleCat.{w} R} (m : M ⊗ N ⟶ P)

def sheafPairing : (S).obj M ⊗ (S).obj N ⟶ (S).obj P :=
  μ S M N ≫ (S).map m

def underlyingPairing : ((S).obj M).obj ⊗ ((S).obj N).obj ⟶ ((S).obj P).obj :=
  μ U ((S).obj M) ((S).obj N) ≫ (U).map (sheafPairing J R m)

theorem unit_pairing :
    ((adj).unit.app M ⊗ₘ (adj).unit.app N) ≫ underlyingPairing J R m =
      m ≫ (adj).unit.app P :=
  adjunction_pairing adj m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.TensorPairing
