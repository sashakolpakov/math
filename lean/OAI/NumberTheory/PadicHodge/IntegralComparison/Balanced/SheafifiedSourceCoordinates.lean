import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

/-! # Sheafified Source Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceCoordinates

noncomputable section

/-! A source-coordinate square for the actual sheafified cone gives the
same coordinate square on canonical Ext-zero sections and on the original
injective-section cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem transported_square {C : Type*} [Category C] {A A' K L I : C}
    (u : A ⟶ A') (a : A ⟶ K) (b : A' ⟶ L) (t : K ≅ L) (g : K ⟶ I)
    (h : a ≫ t.hom = u ≫ b) : u ≫ (b ≫ t.inv ≫ g) = a ≫ g := by
  calc
    _ = (u ≫ b) ≫ t.inv ≫ g := by simp only [Category.assoc]
    _ = (a ≫ t.hom) ≫ t.inv ≫ g := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem comparison_coordinates {A B : Type*} [Category A] [Category B]
    (H : A ⥤ B) {X Y Z : A} {W : B}
    (a : X ⟶ Z) (u : X ⟶ Y) (b : Y ⟶ Z) (v : H.obj Z ⟶ W)
    (h : a = u ≫ b) : H.map a ≫ v = (H.map u ≫ H.map b) ≫ v :=
  (congrArg (fun f => H.map f ≫ v) h).trans
    (congrArg (fun f => f ≫ v) (H.map_comp u b))

universe u z
variable {C : Type u} [Category.{0} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)
  (M' : CochainComplex (ModuleCat.{u} R) ℕ)
  (L : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ)
  (e : M ≅ M') (t : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ≅ L)
  (b : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M' ⟶ L)
  (h : Sheafified.ConstantCochainCoordinates.sheafMap R J M P a ≫ t.hom =
    ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map e.hom ≫ b)

def normalizedSections := ConstantSection.ComplexMap.map R J M' I.cocomplex
  (b ≫ t.inv ≫ g)

abbrev sectionsMap_eq :=
  ConstantSection.ComplexNaturality.naturality R J e.hom g
    (Sheafified.ConstantCochainCoordinates.sheafMap R J M P a) (b ≫ t.inv ≫ g)
    (transported_square _ _ b t g h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceCoordinates
