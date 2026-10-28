import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexData
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal

/-! # Cech Pushforward Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardCoordinates

noncomputable section

/-! The original principal-to-relative Cech coordinate isomorphism
commutes with inverse image of its entire open diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.ReindexData
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
private theorem compose_components {B : Type v} [Category B] {α : Type u} [HasProducts.{u} B]
    {L M N : α → B} (a : ∀ i, L i ≅ M i) (b : ∀ i, M i ≅ N i) (c : ∀ i, L i ≅ N i)
    (h : ∀ i, (a i).hom ≫ (b i).hom = (c i).hom) :
    (Pi.mapIso a).hom ≫ (Pi.mapIso b).hom = (Pi.mapIso c).hom := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.mapIso_hom_π_assoc, h]

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {C : Type u} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι : Type u} [LinearOrder ι] (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : (Opens Y)ᵒᵖ ⥤ A)
attribute [local instance] RelativeCech.ReindexData.preimage_limits

abbrev pulled : C ⥤ Opens Y := F ⋙ RelativeCech.ReindexData.preimage f

local instance pulled_products (n : ℕ) (a : Fin (n+1) → ι) :
    PreservesLimit (Discrete.functor (W ∘ a)) (pulled f F) := by
  dsimp only [pulled]
  infer_instance

omit [Abelian A] [HasCoproducts A] in
theorem component (n : ℕ) :
    (AugmentedCech.AmbientCoordinates.componentIso F W ((RelativeCech.ReindexData.preimage f).op ⋙ P) n).hom ≫
      (AugmentedOrdered.CechReindex.componentIso (RelativeCech.ReindexData.preimage f) (F.obj ∘ W)
        (RelativeCech.Intersections.presheaf ((RelativeCech.ReindexData.preimage f).obj (F.obj (⊤_ C))) P) n).hom =
    (AugmentedCech.AmbientCoordinates.componentIso (pulled f F) W P n).hom := by
  dsimp only [AugmentedCech.AmbientCoordinates.componentIso,
    AugmentedOrdered.CechReindex.componentIso]
  apply compose_components
  intro a
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp]
  congr 1

omit [HasCoproducts A] in
theorem ambient :
    (AugmentedCech.AmbientCoordinates.iso F W ((RelativeCech.ReindexData.preimage f).op ⋙ P)).hom ≫
      (RelativeCech.ReindexData.sourceIso f (F.obj (⊤_ C)) (F.obj ∘ W) P).hom =
    (AugmentedCech.AmbientCoordinates.iso (pulled f F) W P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact component f F W P n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CechPushforwardCoordinates
