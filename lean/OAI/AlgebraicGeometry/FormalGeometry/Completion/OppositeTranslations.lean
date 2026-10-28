import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine

/-! # Opposite Translations -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OppositeTranslations

noncomputable section

/-! In an irreducible algebraic group, opposite translates of a nonempty
open set have a common prescribed rational point after choosing a translation. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]

theorem opposite_translations_meet (U : A.left.Opens) (hU : (U : Set A.left).Nonempty)
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A,
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (x.left (IsLocalRing.closedPoint K)) ∈ U ∧
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom (x.left (IsLocalRing.closedPoint K)) ∈ U := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let j : A.left ≅ A.left := (Over.forget _).mapIso (asIso (GrpObj.inv (X := A)))
  let V : A.left.Opens := (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).hom ⁻¹ᵁ U
  let W : A.left.Opens := j.hom ⁻¹ᵁ V
  have hV : (V : Set A.left).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    exact ⟨(Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).inv y, by
      change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).hom ((Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).inv y) ∈ U
      rwa [Scheme.inv_hom_apply]⟩
  have hW : (W : Set A.left).Nonempty := by
    obtain ⟨y, hy⟩ := hV
    exact ⟨j.inv y, by
      change j.hom (j.inv y) ∈ V
      rwa [Scheme.inv_hom_apply]⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter V.isOpen W.isOpen hV hW) (V ⊓ W).isOpen.isLocallyClosed
  let a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom z hzc) (pointOfClosedPoint_comp A.hom z hzc)
  have ha : a.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply A.hom z hzc _
  have hinv : (a⁻¹).left (IsLocalRing.closedPoint K) = j.hom z := by
    change (a.left ≫ j.hom) (IsLocalRing.closedPoint K) = j.hom z
    rw [Scheme.Hom.comp_apply, ha]
  refine ⟨a, ?_, ?_⟩
  · have he := congrArg (fun t : Spec (CommRingCat.of K) ⟶ A.left =>
        t (IsLocalRing.closedPoint K)) (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A x a)
    change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (x.left (IsLocalRing.closedPoint K)) ∈ U
    rw [show (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (x.left (IsLocalRing.closedPoint K)) =
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).hom (a.left (IsLocalRing.closedPoint K)) from he, ha]
    exact hz.1
  · have he := congrArg (fun t : Spec (CommRingCat.of K) ⟶ A.left =>
        t (IsLocalRing.closedPoint K)) (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A x a⁻¹)
    rw [show (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom (x.left (IsLocalRing.closedPoint K)) =
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A x).hom ((a⁻¹).left (IsLocalRing.closedPoint K)) from he, hinv]
    exact hz.2

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OppositeTranslations
