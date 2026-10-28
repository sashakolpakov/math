import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Coefficient Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange

noncomputable section

/-!
# Changing coefficients in the Čech complex

An additive functor preserving products commutes with Čech cochains.
This applies to restriction of presheaves to an open subscheme and is
used to compare the global construction with its local contractions.
-/

open _root_.CategoryTheory Limits Opposite Simplicial _root_.AlgebraicTopology

universe w v vA vB u uA uB

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)

theorem piComparison_natural {α β : Type w} (X : α → A) (Y : β → A)
    (f : β → α) (a : ∀ j, X (f j) ⟶ Y j) :
    G.map (Pi.lift (fun j => Pi.π X (f j) ≫ a j)) ≫ piComparison G Y =
      piComparison G X ≫ Pi.lift (fun j => Pi.π (fun i => G.obj (X i)) (f j) ≫ G.map (a j)) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_comp_π,
    ← G.map_comp]
  rw [piComparison_comp_π_assoc, G.map_comp]

variable {C : Type u} [Category.{v} C]
  (E : SimplicialObject (FormalCoproduct.{w} C)) (P : Cᵒᵖ ⥤ A)
  [PreservesLimitsOfSize.{w, w} G]

def cosimplicialIso :
    (FormalCoproduct.cosimplicialObjectFunctor E).obj P ⋙ G ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj (P ⋙ G) :=
  NatIso.ofComponents (fun n => PreservesProduct.iso G
    (fun i : (E.obj (op n)).I => P.obj (op ((E.obj (op n)).obj i)))) (by
      intro n m f
      let En := E.obj (op n)
      let Em := E.obj (op m)
      let φ : Em ⟶ En := E.map f.op
      exact piComparison_natural G (fun i : En.I => P.obj (op (En.obj i)))
        (fun i : Em.I => P.obj (op (Em.obj i))) φ.f (fun i => P.map (φ.φ i).op))

variable [Preadditive A] [Preadditive B] [G.Additive]

omit [HasProducts.{w} A] [HasProducts.{w} B] [PreservesLimitsOfSize.{w, w} G] in
theorem map_cofaceD (Y : CosimplicialObject A) (n : ℕ) :
    G.map (AlternatingCofaceMapComplex.objD Y n) = AlternatingCofaceMapComplex.objD (Y ⋙ G) n := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

def mapCofaceIso (Y : CosimplicialObject A) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj Y) ≅
      AlternatingCofaceMapComplex.obj (Y ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    have h0 : (AlternatingCofaceMapComplex.obj (Y ⋙ G)).d n (n + 1) =
        AlternatingCofaceMapComplex.objD (Y ⋙ G) n :=
      CochainComplex.of_d (fun i => (Y ⋙ G).obj ⦋i⦌) (AlternatingCofaceMapComplex.objD (Y ⋙ G)) n
    have h1 : (AlternatingCofaceMapComplex.obj Y).d n (n + 1) = AlternatingCofaceMapComplex.objD Y n :=
      CochainComplex.of_d (fun i => Y.obj ⦋i⦌) (AlternatingCofaceMapComplex.objD Y) n
    exact (Category.id_comp _).trans ((h0.trans ((map_cofaceD G Y n).symm.trans
      (congrArg G.map h1).symm)).trans (Category.comp_id _).symm))

/-- Product-preserving additive change of coefficients commutes with the Čech complex. -/
def complexIso :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((FormalCoproduct.cochainComplexFunctor E).obj P) ≅
      (FormalCoproduct.cochainComplexFunctor E).obj (P ⋙ G) :=
  mapCofaceIso G ((FormalCoproduct.cosimplicialObjectFunctor E).obj P) ≪≫
    (alternatingCofaceMapComplex B).mapIso (cosimplicialIso G E P)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange
