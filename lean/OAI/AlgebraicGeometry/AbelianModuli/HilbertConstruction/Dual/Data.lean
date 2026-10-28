import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

noncomputable section

/-!
The meaning of a dual abelian scheme with normalized Poincare data. The
represented functor is the concrete homogeneous Picard sheaf constructed
in HomogeneousPicard. This definition does not postulate the existence
of a dual or of a moduli scheme. A dual is specified by its usual universal
property, and its underlying representing scheme is proved unique.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}}

/-- A dual abelian scheme and its actual normalized Poincare line bundle. -/
structure DualAbelianData (A : Abelian.Schemes.AbelianScheme g S) where
  abelian : Abelian.Schemes.AbelianScheme g S
  representable : A.homogeneousPicardSheaf.obj.RepresentableBy abelian.scheme
  origin : ∀ T : Over S,
    representable.homEquiv (1 : T ⟶ abelian.scheme) =
      A.trivialHomogeneousPicardClass T
  poincare : Line.Bundles.LineBundle ((abelian.scheme ⊗ A.scheme).left)
  poincareHomogeneous : A.IsHomogeneousPicardClass abelian.scheme
    (Quotient.mk (Line.Bundles.LineBundle.isoSetoid _) poincare)
  universalClass : representable.homEquiv (𝟙 abelian.scheme) =
    (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
      (.op abelian.scheme) ⟨Quotient.mk (Line.Bundles.LineBundle.isoSetoid _) poincare,
        poincareHomogeneous⟩
  normalizedAtAbelianZero : Nonempty
    ((Line.Bundles.LineBundle.pullback
        (lift (𝟙 abelian.scheme) (1 : abelian.scheme ⟶ A.scheme)).left poincare).sheaf ≅
      Line.Bundles.structureModule abelian.scheme.left)
  normalizedAtDualZero : Nonempty
    ((Line.Bundles.LineBundle.pullback
        (lift (1 : A.scheme ⟶ abelian.scheme) (𝟙 A.scheme)).left poincare).sheaf ≅
      Line.Bundles.structureModule A.scheme.left)

/-- The representing scheme underlying the dual is unique up to isomorphism. -/
def DualAbelianData.uniqueUnderlyingIso {A : Abelian.Schemes.AbelianScheme g S}
    (D E : DualAbelianData A) : D.abelian.scheme ≅ E.abelian.scheme :=
  D.representable.uniqueUpToIso E.representable

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
