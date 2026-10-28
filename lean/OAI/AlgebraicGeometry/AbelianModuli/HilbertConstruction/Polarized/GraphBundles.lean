import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Graph Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical graph bundle on a polarized family is compatible with base change and polarized isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme.{u}}

def PolarizationData.PolarizedAbelianWithFullLevel.graphBundle (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Line.Bundles.LineBundle A.abelian.scheme.left :=
  PoincareGraph.Bundles.poincareGraphBundle A.dual A.polarization.isogeny.hom

def PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_zeroIso
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    (Line.Bundles.LineBundle.pullback η[A.abelian.scheme].left A.graphBundle).sheaf ≅ Line.Bundles.structureModule S :=
  PoincareGraph.Fibers.poincareGraphBundle_zeroIso A.dual A.polarization.isogeny.hom

def PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_baseChangeIso
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S) :
    (A.pullback f).graphBundle.sheaf ≅
      (Line.Bundles.LineBundle.pullback (pullback.fst A.abelian.scheme.hom f) A.graphBundle).sheaf :=
  PoincareGraph.Bundles.poincareGraphBundle_baseChangeIso A.dual A.polarization.isogeny.hom f

theorem Polarized.GraphBundles.poincareGraphMap_natural {A B D E : Over S} (p : A ⟶ D) (q : B ⟶ E)
    (a : A ⟶ B) (d : D ⟶ E) (h : p ≫ d = a ≫ q) :
    lift p (𝟙 A) ≫ (d ⊗ₘ a) = a ≫ lift q (𝟙 B) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst, h]
  · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd,
      Category.id_comp, Category.comp_id]

theorem Moduli.Isomorphisms.LevelPreservingIso.graphBundle_class {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) :
    Line.Bundles.LineBundle.pullbackClass e.abelian.hom.left (Line.Bundles.LineBundle.classOf B.graphBundle) =
      Line.Bundles.LineBundle.classOf A.graphBundle := by
  let a := PoincareGraph.Bundles.poincareGraphMap A.dual A.polarization.isogeny.hom
  let b := PoincareGraph.Bundles.poincareGraphMap B.dual B.polarization.isogeny.hom
  let d := e.dual.hom ⊗ₘ e.abelian.hom
  have h : a.left ≫ d.left = e.abelian.hom.left ≫ b.left :=
    congrArg Over.Hom.left (Polarized.GraphBundles.poincareGraphMap_natural A.polarization.isogeny.hom
      B.polarization.isogeny.hom e.abelian.hom e.dual.hom e.polarization)
  change Line.Bundles.LineBundle.pullbackClass e.abelian.hom.left
    (Line.Bundles.LineBundle.pullbackClass b.left (Line.Bundles.LineBundle.classOf B.dual.poincare)) =
      Line.Bundles.LineBundle.pullbackClass a.left (Line.Bundles.LineBundle.classOf A.dual.poincare)
  exact (Line.Bundles.LineBundle.pullbackClass_comp e.abelian.hom.left b.left _).symm.trans
    ((congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf B.dual.poincare)) h.symm).trans
      ((Line.Bundles.LineBundle.pullbackClass_comp a.left d.left _).trans
        (congrArg (Line.Bundles.LineBundle.pullbackClass a.left) e.poincare)))

def Moduli.Isomorphisms.LevelPreservingIso.graphBundleIso {A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : Moduli.Isomorphisms.LevelPreservingIso A B) :
    (Line.Bundles.LineBundle.pullback e.abelian.hom.left B.graphBundle).sheaf ≅ A.graphBundle.sheaf :=
  Classical.choice (Quotient.exact e.graphBundle_class)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
