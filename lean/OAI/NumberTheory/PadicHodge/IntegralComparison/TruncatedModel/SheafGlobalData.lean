import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AffineSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryGlobal

/-! # Sheaf Global Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobalData.Comparison

noncomputable section

section

/-! The original global comparison is the map of the genuine de Rham
and resolution sheaf complexes, through the original small-cover
ordinary coordinates and their canonical section units. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def restriction : Sheaf (Opens.grothendieckTopology X.left)
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ⥤
      (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) _ ⋙
    GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)

instance restriction_additive : (restriction p k n X).Additive := by
  dsimp only [restriction]
  infer_instance

def unit : OrdinarySectionMap.Ordinary.source p k n X ⟶
    ((restriction p k n X).mapHomologicalComplex (.up ℕ)).obj
      (ModelSheafComparison.source p k n X) :=
  (GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso (OrdinarySectionMap.Ordinary.coefficients p k n)
      (Small.OrdinaryCechTotal.Ordinary.diagram (Truncated.Witt.Ring p k n) X)).hom ≫
    ((GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves
      (OrdinarySectionMap.Ordinary.coefficients p k n)).mapHomologicalComplex (.up ℕ)).map
        ((Small.OrdinaryCechTotal.Ordinary.complexIso (Truncated.Witt.Ring p k n) X).hom ≫
          ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex
            (.up ℕ)).map (IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit (Truncated.Witt.Ring p k n) X))

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem unit_component (U : X.left.affineOpens) (q : ℕ) :
    ((unit p k n X).f q).app (op U) =
      (OrdinarySectionMap.Ordinary.coefficients p k n).map
        ((IntrinsicDeRham.SectionUnit.Intrinsic.unit (Truncated.Witt.Ring p k n) X U.val).f q) := by
  change 𝟙 _ ≫ (OrdinarySectionMap.Ordinary.coefficients p k n).map
    ((𝟙 _ ≫ 𝟙 _) ≫ _) = (OrdinarySectionMap.Ordinary.coefficients p k n).map (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  rfl

def affineMap :
    ((restriction p k n X).mapHomologicalComplex (.up ℕ)).obj
      (ModelSheafComparison.source p k n X) ⟶
    ((SectionBifunctor.sections p k n X Y f).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex :=
  ((restriction p k n X).mapHomologicalComplex (.up ℕ)).map
    (ModelSheafComparison.map p k n X Y f hp I)

theorem affine_comparison :
    unit p k n X ≫ affineMap p k n X Y f hp I =
      OrdinarySectionMap.Ordinary.map p k n X Y f hp I := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  rw [comp_f, NatTrans.comp_app, unit_component]
  have h := AffineSheaf.Comparison.unit_affine p k n X Y f hp I U.unop q
  refine h.trans ?_
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

def totalUnit :
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).obj
      (OrdinarySectionMap.Ordinary.source p k n X) ⟶
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).obj
      (((restriction p k n X).mapHomologicalComplex (.up ℕ)).obj
        (ModelSheafComparison.source p k n X)) :=
  (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map (unit p k n X)

def totalMap :
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).obj
      (((restriction p k n X).mapHomologicalComplex (.up ℕ)).obj
        (ModelSheafComparison.source p k n X)) ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map
    (affineMap p k n X Y f hp I)

end

/-! The actual total map of the global sheaf comparison agrees with
its original affine ordinary comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapped_comp {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c :=
  (F.map_comp a b).symm.trans (congrArg F.map h)

private theorem insert_factor {C : Type*} [Category C] {A B D E F : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : B ⟶ E} {e : E ⟶ F} {f : A ⟶ F}
    (h : b ≫ c = d) (hf : a ≫ d ≫ e = f) : a ≫ b ≫ c ≫ e = f := by
  rw [← Category.assoc b c e, h]
  exact hf

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

omit [Fintype k] [CharP k p] in
private theorem total_composition
    {K L M : CochainComplex (X.left.affineOpensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    {a : K ⟶ L} {b : L ⟶ M} {d : K ⟶ M} (h : a ≫ b = d) :
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map a ≫
      (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map b =
    (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X).map d :=
  mapped_comp (OrdinaryGlobal.OrdinaryComparison.totalFunctor p k n X) h

theorem comparison : totalUnit p k n X ≫ totalMap p k n X Y f hp I =
    OrdinaryGlobal.OrdinaryComparison.map p k n X Y f hp I :=
  total_composition p k n X
    (affine_comparison p k n X Y f hp I)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafGlobalData.Comparison
