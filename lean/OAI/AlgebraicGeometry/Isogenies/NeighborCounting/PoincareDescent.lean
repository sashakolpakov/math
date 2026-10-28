import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareFamilyCompatibility
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullHomCommonFactor
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareAffineCover
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineHomDescent

/-! # Poincare Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent

noncomputable section

/-! Actual global comparison of the independently specified Poincare
bundles. Compatibility on arbitrary schemes follows by factoring their
test maps through one graph, so nilpotent tests are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareCocycle
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareFamilyCompatibility.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareAffineCover

variable {k : Type u} [Field k] [IsAlgClosed k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem poincareLocal_compatible {T : Over (Spec (.of k))} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) :
    FramedDescent.CompatibleHom (t ▷ A.scheme).left
      (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht).hom := by
  intro Z x y p hx hy
  let xB := ProductTestFactors.baseMap A.scheme t p x hx
  let yB := ProductTestFactors.baseMap A.scheme t p y hy
  let pB := ProductTestFactors.baseTarget A.scheme p
  have hxB : xB ≫ t = pB := ProductTestFactors.baseMap_comp A.scheme t p x hx
  have hyB : yB ≫ t = pB := ProductTestFactors.baseMap_comp A.scheme t p y hy
  exact PullHomCommonFactor.native_common_factor (t ▷ A.scheme).left
    (PoincareNormalization.normalizedPoincareLocalIso DA DB f t ht).hom
    (xB ▷ A.scheme).left (yB ▷ A.scheme).left (pB ▷ A.scheme).left
    (PoincareFamilyCompatibility.Family.product_comp DB t xB pB hxB) (PoincareFamilyCompatibility.Family.product_comp DB t yB pB hyB)
    (PoincareFamilyCompatibility.Family.poincareFamily_compatible DA DB f t ht xB yB pB hxB hyB)
    (ProductTestFactors.graph A.scheme p).left x y p
    (ProductTestFactors.graph_to_test A.scheme t p x hx) (ProductTestFactors.graph_to_test A.scheme t p y hy)
    (ProductTestFactors.graph_to_target A.scheme p) hx hy

theorem existsUnique_poincareIso :
    ∃! e : (PoincareCocycle.abelianGlobalBundle DB f).sheaf ≅ (PoincareCocycle.dualGlobalBundle DA DB f).sheaf,
      (Scheme.Modules.pullback (PoincareAffineCover.affineCoverMap DA DB f ▷ A.scheme).left).mapIso e =
        PoincareNormalization.normalizedPoincareLocalIso DA DB f (PoincareAffineCover.affineCoverMap DA DB f)
          (PoincareAffineCover.affineCoverMap_member DA DB f) :=
  LineHomDescent.existsUnique_lineIso_descent
    (PoincareAffineCover.affineCoverMap DA DB f ▷ A.scheme).left
    (PoincareCocycle.abelianGlobalBundle DB f).locallyTrivial (PoincareCocycle.dualGlobalBundle DA DB f).locallyTrivial
    (PoincareNormalization.normalizedPoincareLocalIso DA DB f (PoincareAffineCover.affineCoverMap DA DB f)
      (PoincareAffineCover.affineCoverMap_member DA DB f))
    (poincareLocal_compatible DA DB f (PoincareAffineCover.affineCoverMap DA DB f) (PoincareAffineCover.affineCoverMap_member DA DB f))

def poincareIso : (PoincareCocycle.abelianGlobalBundle DB f).sheaf ≅ (PoincareCocycle.dualGlobalBundle DA DB f).sheaf :=
  (existsUnique_poincareIso DA DB f).exists.choose

theorem poincareIso_pullback :
    (Scheme.Modules.pullback (PoincareAffineCover.affineCoverMap DA DB f ▷ A.scheme).left).mapIso
        (poincareIso DA DB f) =
      PoincareNormalization.normalizedPoincareLocalIso DA DB f (PoincareAffineCover.affineCoverMap DA DB f)
        (PoincareAffineCover.affineCoverMap_member DA DB f) :=
  (existsUnique_poincareIso DA DB f).exists.choose_spec

theorem poincareClass_eq :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareCocycle.abelianGlobalBundle DB f) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareCocycle.dualGlobalBundle DA DB f) :=
  Quotient.sound ⟨poincareIso DA DB f⟩

/-- An actual global isomorphism respecting the fixed zero trivializations. -/
def normalizedGlobalPoincareIso :
    (PoincareCocycle.abelianGlobalBundle DB f).sheaf ≅ (PoincareCocycle.dualGlobalBundle DA DB f).sheaf :=
  RigidifiedIso.normalizedIso (fst DB.abelian.scheme A.scheme).left
    (PoincareNormalization.familyZero A DB.abelian.scheme).left (poincareIso DA DB f)
    (PoincareNormalization.abelianGlobalZeroIso DB f) (PoincareNormalization.dualGlobalZeroIso DA DB f)

theorem normalizedGlobalPoincareIso_section :
    (Scheme.Modules.pullback (PoincareNormalization.familyZero A DB.abelian.scheme).left).map
        (normalizedGlobalPoincareIso DA DB f).hom ≫ (PoincareNormalization.dualGlobalZeroIso DA DB f).hom =
      (PoincareNormalization.abelianGlobalZeroIso DB f).hom :=
  RigidifiedIso.normalizedIso_section (fst DB.abelian.scheme A.scheme).left
    (PoincareNormalization.familyZero A DB.abelian.scheme).left (PoincareNormalization.familyZero_projection A DB.abelian.scheme)
    (poincareIso DA DB f) (PoincareNormalization.abelianGlobalZeroIso DB f) (PoincareNormalization.dualGlobalZeroIso DA DB f)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent
