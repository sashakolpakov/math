import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualIs
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-! # Quotient Dual Source Poincare -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualSourcePoincare.Construction

noncomputable section

/-! The pulled-back original Poincare line is a normalized actual line
representing the quotient-dual universal class on the finite cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualSourcePoincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.abelian.scheme ⊗ B.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (D.abelian.scheme ◁ f.hom).left D.poincare

omit [IsAlgClosed k] in
theorem quotientDualSourcePoincare_homogeneous :
    B.IsHomogeneousPicardClass D.abelian.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualSourcePoincare D f)) :=
  Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardClass_pullback B A f.hom D.poincareHomogeneous

omit [IsAlgClosed k] in
theorem quotientDualSourcePoincare_normalized :
    Isogenies.NeighborCounting.PoincareNormalization.IsNormalized B D.abelian.scheme (quotientDualSourcePoincare D f) :=
  Isogenies.NeighborCounting.PoincareNormalization.abelianPull_normalized D f.hom

theorem quotientDualSourcePoincare_class :
    (QuotientDualIs.Construction.quotientDualRepresentable D f r).homEquiv (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app
        (.op D.abelian.scheme)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualSourcePoincare D f), quotientDualSourcePoincare_homogeneous D f⟩ := by
  have hp := QuotientDualIs.Construction.quotientDualRepresentable_projection D f r D.abelian.scheme (𝟙 D.abelian.scheme)
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Scheme.fppfTopology.over (Spec (.of k)))
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf B A f.hom)) (.op D.abelian.scheme))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩
  exact (congrArg (QuotientDualIs.Construction.quotientDualRepresentable D f r).homEquiv
      (Category.id_comp (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection)).symm.trans
    (hp.trans ((congrArg ((Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op D.abelian.scheme))
      D.universalClass).trans hu.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualSourcePoincare.Construction
