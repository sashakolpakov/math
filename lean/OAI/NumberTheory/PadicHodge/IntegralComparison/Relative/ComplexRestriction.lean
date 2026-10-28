import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex

/-! # Complex Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction

noncomputable section

/-!
# IntegralComparison: restriction of the original relative crystalline complex to an indexing subcategory
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w v' w'

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (t : D ⥤ C)

def restriction : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} B) :=
  (Functor.whiskeringLeft _ _ _).obj t.op

instance restriction_additive : (restriction (B := B) t).Additive where
  map_add := by intros; rfl

def formsIso (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (n : ℕ) :
    (restriction (B := B) t).obj (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π n) ≅
      RelativeCrystalline.ModuleMaps.formsPresheaf (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π) n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    rfl)

def complexIso (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) :
    ((restriction (B := B) t).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (RelativeCrystalline.ModuleComplex.complex H Q π) ≅
    RelativeCrystalline.ModuleComplex.complex (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π) :=
  HomologicalComplex.Hom.isoOfComponents (formsIso t H Q π) (by
    intro n m h
    change n + 1 = m at h
    subst m
    change (formsIso t H Q π n).hom ≫
        (RelativeCrystalline.ModuleComplex.complex (t ⋙ H) (t ⋙ Q) (Functor.whiskerLeft t π)).d n (n + 1) =
      (restriction (B := B) t).map ((RelativeCrystalline.ModuleComplex.complex H Q π).d n (n + 1)) ≫
        (formsIso t H Q π (n + 1)).hom
    rw [RelativeCrystalline.ModuleComplex.complex_d, RelativeCrystalline.ModuleComplex.complex_d]
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
