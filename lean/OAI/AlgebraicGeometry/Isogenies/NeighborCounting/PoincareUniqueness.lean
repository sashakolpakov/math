import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings

/-! # Poincare Uniqueness -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareUniqueness

noncomputable section

/-! The comparison on the constructed cover is the unique normalized
comparison of the independently given native Poincare bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedUniqueness

variable {k : Type u} [Field k] [IsAlgClosed k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem normalizedPoincareLocalIso_unique (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t)
    (e : (PoincareNormalization.abelianLocalBundle DB f t).sheaf ≅ (PoincareNormalization.dualLocalBundle DA DB f t).sheaf)
    (he : (Scheme.Modules.pullback (PoincareNormalization.familyZero A T).left).map e.hom ≫
      (PoincareNormalization.dualLocalZeroIso DA DB f t).hom = (PoincareNormalization.abelianLocalZeroIso DB f t).hom) :
    e = PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht := by
  have : IsIntegral A.scheme.left :=
    AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected A.scheme.hom
  exact RigidifiedUniqueness.proper_product_normalizedIso_unique T A.scheme
    (PoincareNormalization.familyZero A T).left (PoincareNormalization.familyZero_projection A T)
    (PoincareNormalization.abelianLocalBundle DB f t).locallyTrivial
    (PoincareNormalization.abelianLocalZeroIso DB f t) (PoincareNormalization.dualLocalZeroIso DA DB f t) e _ he
    (PoincareNormalization.normalizedPoincareLocalIso_section DA DB f t ht)

/-- Every member of the derived fppf cover has exactly one normalized
isomorphism, including members with nonreduced underlying schemes. -/
theorem existsUnique_normalizedPoincareLocalIso (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) :
    ∃! e : (PoincareNormalization.abelianLocalBundle DB f t).sheaf ≅ (PoincareNormalization.dualLocalBundle DA DB f t).sheaf,
      (Scheme.Modules.pullback (PoincareNormalization.familyZero A T).left).map e.hom ≫
        (PoincareNormalization.dualLocalZeroIso DA DB f t).hom = (PoincareNormalization.abelianLocalZeroIso DB f t).hom :=
  ⟨PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht, PoincareNormalization.normalizedPoincareLocalIso_section DA DB f t ht,
    fun e he ↦ normalizedPoincareLocalIso_unique DA DB f t ht e he⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareUniqueness
