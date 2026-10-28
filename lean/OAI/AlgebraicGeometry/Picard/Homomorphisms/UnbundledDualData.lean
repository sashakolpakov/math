import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

/-! # Unbundled Dual Data -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard

noncomputable section

/-! Normalized Poincare data without a global dimension parameter.
The fixed-dimension API is recovered by supplying the actual smooth
relative dimension, without changing the represented Picard functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
open scoped _root_.CategoryTheory.MonObj

universe u

structure DualData {S : Scheme.{u}} (A : Over S) [GrpObj A] where
  abelian : Over S
  group : GrpObj abelian
  commutative : IsCommMonObj abelian
  proper : IsProper abelian.hom
  smooth : Smooth abelian.hom
  connected : GeometricallyConnected abelian.hom
  representable : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.RepresentableBy abelian
  origin : ∀ T : Over S,
    representable.homEquiv (1 : T ⟶ abelian) = UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A T
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((abelian ⊗ A).left)
  poincareHomogeneous : UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf poincare)
  universalClass : representable.homEquiv (𝟙 abelian) =
    (toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (.op abelian)
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf poincare, poincareHomogeneous⟩
  normalizedAtAbelianZero : Nonempty
    ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (lift (𝟙 abelian) (1 : abelian ⟶ A)).left poincare).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule abelian.left)
  normalizedAtDualZero : Nonempty
    ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (lift (1 : A ⟶ abelian) (𝟙 A)).left poincare).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

attribute [instance] DualData.group DualData.commutative DualData.proper DualData.smooth DualData.connected

def DualData.ofBundled {S : Scheme.{u}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) : DualData A.scheme where
  abelian := D.abelian.scheme
  group := D.abelian.group
  commutative := D.abelian.commutative
  proper := D.abelian.proper
  smooth := inferInstance
  connected := D.abelian.connected
  representable := D.representable
  origin := D.origin
  poincare := D.poincare
  poincareHomogeneous := D.poincareHomogeneous
  universalClass := D.universalClass
  normalizedAtAbelianZero := D.normalizedAtAbelianZero
  normalizedAtDualZero := D.normalizedAtDualZero

def DualData.abelianOfDimension {S : Scheme.{u}} {A : Over S} [GrpObj A]
    (D : DualData A) (g : ℕ) (hdim : SmoothOfRelativeDimension g D.abelian.hom) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S where
  scheme := D.abelian
  group := D.group
  commutative := D.commutative
  proper := D.proper
  smoothDimension := hdim
  connected := D.connected

def DualData.toBundled {S : Scheme.{u}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : DualData A.scheme)
    (hdim : SmoothOfRelativeDimension g D.abelian.hom) : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A where
  abelian := D.abelianOfDimension g hdim
  representable := D.representable
  origin := D.origin
  poincare := D.poincare
  poincareHomogeneous := D.poincareHomogeneous
  universalClass := D.universalClass
  normalizedAtAbelianZero := D.normalizedAtAbelianZero
  normalizedAtDualZero := D.normalizedAtDualZero

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard
