import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Poincare Local -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal

noncomputable section

/-! Local isomorphisms of the independently specified Poincare bundles.
The covering sieve is derived from representability and sheafification;
no Poincare comparison is an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PicardMaps OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison

variable {S : Scheme.{u}} {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

/-- The Poincare bundle pulled back along the original abelian morphism. -/
def abelianPullClass (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    A.homogeneousPicardPresheaf.obj (op DB.abelian.scheme) :=
  (PicardMaps.homogeneousPicardPull f).app (op DB.abelian.scheme)
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare, DB.poincareHomogeneous⟩

/-- The independently specified Poincare bundle on the source dual,
pulled back along the dual map constructed by representability. -/
def dualPullClass (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    A.homogeneousPicardPresheaf.obj (op DB.abelian.scheme) :=
  A.homogeneousPicardPresheaf.map (DualComparison.dualMap DA DB f).op
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare, DA.poincareHomogeneous⟩

theorem poincare_sheafification_eq (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
        (op DB.abelian.scheme) (abelianPullClass DB f) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
        (op DB.abelian.scheme) (dualPullClass DA DB f) := by
  let qB : B.homogeneousPicardPresheaf.obj (op DB.abelian.scheme) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare, DB.poincareHomogeneous⟩
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (PicardMaps.homogeneousPicardPull_toSheaf f) (op DB.abelian.scheme)) qB
  have hd := DualComparison.dualMap_action DA DB f (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, DB.universalClass] at hd
  exact hn.trans (hd.symm.trans (DualComparison.representable_poincare DA (DualComparison.dualMap DA DB f)))

/-- The actual fppf covering sieve where the two raw line-bundle classes agree. -/
def poincareComparisonCover (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (Scheme.fppfTopology.over S).Cover DB.abelian.scheme :=
  ⟨Presheaf.equalizerSieve (F := A.homogeneousPicardPresheaf)
      (X := op DB.abelian.scheme) (abelianPullClass DB f) (dualPullClass DA DB f),
    Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf)
      _ _ (poincare_sheafification_eq DA DB f)⟩

theorem poincare_local_class_eq (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (t : T ⟶ DB.abelian.scheme)
    (ht : (poincareComparisonCover DA DB f).1 t) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ▷ A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ▷ A.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DualComparison.dualMap DA DB f ▷ A.scheme).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) :=
  congrArg Subtype.val ht

/-- Each member of the constructed cover carries an actual module-sheaf
isomorphism, before passing to either Picard sheafification. -/
def poincareLocalIso (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (t : T ⟶ DB.abelian.scheme)
    (ht : (poincareComparisonCover DA DB f).1 t) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare)).sheaf ≅
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare)).sheaf :=
  Classical.choice (Quotient.exact (poincare_local_class_eq DA DB f t ht))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal
