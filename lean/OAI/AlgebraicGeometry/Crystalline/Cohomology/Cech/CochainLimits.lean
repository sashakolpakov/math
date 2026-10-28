import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Cochain Limits -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits

noncomputable section

/-!
# Limits in each degree of the actual Čech cochain functor

Each degree is the product of evaluations on the corresponding nerve
objects. Expressing this as a restriction followed by a limit proves
preservation of kernels, as required in cochain correction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [Preadditive A]
  (E : SimplicialObject (FormalCoproduct.{w} C))

def indices (n : ℕ) : Discrete (E.obj (op ⦋n⦌)).I ⥤ Cᵒᵖ :=
  Discrete.functor (fun i => op ((E.obj (op ⦋n⦌)).obj i))

def productDegree (n : ℕ) : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ A).obj (indices E n) ⋙ lim

def diagramIso (n : ℕ) (P : Cᵒᵖ ⥤ A) :
    Discrete.functor (fun i => P.obj (op ((E.obj (op ⦋n⦌)).obj i))) ≅ indices E n ⋙ P :=
  Discrete.natIso (fun _ => Iso.refl _)

def componentIso (n : ℕ) (P : Cᵒᵖ ⥤ A) :
    ∏ᶜ (fun i => P.obj (op ((E.obj (op ⦋n⦌)).obj i))) ≅ limit (indices E n ⋙ P) :=
  HasLimit.isoOfNatIso (diagramIso E n P)

omit [Preadditive A] in
theorem component_pi (n : ℕ) (P : Cᵒᵖ ⥤ A) (i : Discrete (E.obj (op ⦋n⦌)).I) :
    (componentIso E n P).hom ≫ limit.π (indices E n ⋙ P) i =
      Limits.Pi.π (fun i => P.obj (op ((E.obj (op ⦋n⦌)).obj i))) i.as :=
  (HasLimit.isoOfNatIso_hom_π (diagramIso E n P) i).trans (Category.comp_id _)

def degreeIso (n : ℕ) :
    FormalCoproduct.cochainComplexFunctor E ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      productDegree E n :=
  NatIso.ofComponents (fun P => componentIso E n P) (by
    intro F G f
    apply limit.hom_ext
    intro i
    change (Limits.Pi.map (fun i => f.app (op ((E.obj (op ⦋n⦌)).obj i))) ≫
      (componentIso E n G).hom) ≫ limit.π (indices E n ⋙ G) i =
      ((componentIso E n F).hom ≫
        lim.map (Functor.whiskerLeft (indices E n) f)) ≫ limit.π (indices E n ⋙ G) i
    let φ := Limits.Pi.map (fun i => f.app (op ((E.obj (op ⦋n⦌)).obj i)))
    have hg := component_pi E n G i
    have hf := component_pi E n F i
    have hl := limMap_π (Functor.whiskerLeft (indices E n) f) i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => φ ≫ t) hg).trans
        ((Limits.Pi.map_π _ i.as).trans
          ((congrArg (fun t => t ≫ f.app (op ((E.obj (op ⦋n⦌)).obj i.as))) hf).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun t => (componentIso E n F).hom ≫ t) hl).symm.trans
                (Category.assoc _ _ _).symm))))))

instance productDegree_preservesLimits [HasLimits A] (n : ℕ) : PreservesLimits (productDegree (A := A) E n) := by
  dsimp [productDegree]
  infer_instance

instance degree_preservesLimits [HasLimits A] (n : ℕ) :
    PreservesLimits (FormalCoproduct.cochainComplexFunctor E ⋙
      HomologicalComplex.eval A (ComplexShape.up ℕ) n) :=
  preservesLimits_of_natIso (degreeIso (A := A) E n).symm

instance cochain_additive : (FormalCoproduct.cochainComplexFunctor (A := A) E).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun i => (f + g).app (op ((E.obj (op ⦋n⦌)).obj i))) =
      Limits.Pi.map (fun i => f.app (op ((E.obj (op ⦋n⦌)).obj i))) +
        Limits.Pi.map (fun i => g.app (op ((E.obj (op ⦋n⦌)).obj i)))
    apply Limits.Pi.hom_ext
    intro i
    simp [Preadditive.add_comp, Preadditive.comp_add]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits
