import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex

/-! # Reindex Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCoordinates

noncomputable section

/-! Coordinates for an ordered reindexing followed by a literal
identification of the resulting family of opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (V : ι → D) (h : r.obj ∘ U = V)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

def familyIso : Projection.complex U (r.op ⋙ P) ≅
    Projection.complex V P :=
  Reindex.iso r U P ≪≫ eqToIso (congrArg (fun W => Projection.complex W P) h)

def familyFactorIso {n : ℕ} (a : Projection.Index (ι := ι) n) :
    r.obj (∏ᶜ (U ∘ a.val)) ≅ ∏ᶜ (V ∘ a.val) :=
  PreservesProduct.iso r (U ∘ a.val) ≪≫
    eqToIso (congrArg (fun W => ∏ᶜ (W ∘ a.val)) h)

theorem family_hom_f (n : ℕ) : (familyIso r U V h P).hom.f n =
    (Pi.mapIso (fun a : Projection.Index (ι := ι) n =>
      P.mapIso (familyFactorIso r U V h a).symm.op)).hom := by
  subst V
  simp only [familyIso, familyFactorIso, eqToIso_refl, Iso.trans_refl]
  rfl

theorem family_naturality {Q : Dᵒᵖ ⥤ A} (a : P ⟶ Q) :
    OrderedCech.Functor.Projection.complexMap U (Functor.whiskerLeft r.op a) ≫
        (familyIso r U V h Q).hom =
      (familyIso r U V h P).hom ≫ OrderedCech.Functor.Projection.complexMap V a := by
  subst V
  simpa only [familyIso, eqToIso_refl, Iso.trans_refl] using Reindex.naturality r U P a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCoordinates
