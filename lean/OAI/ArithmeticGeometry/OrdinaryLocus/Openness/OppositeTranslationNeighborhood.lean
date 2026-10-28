import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleSymmetrization
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine

/-! # Opposite Translation Neighborhood -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OppositeTranslationNeighborhood.Construction

noncomputable section

/-! Opposite translates of any nonempty open give neighborhoods of every point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]

theorem exists_opposite_translate_rational
    (U : A.left.Opens) (hU : (U : Set A.left).Nonempty)
    (b : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    ∃ a : 𝟙_ (Over (Spec (.of K))) ⟶ A,
      b.left (IsLocalRing.closedPoint K) ∈
        (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom ⁻¹ᵁ U ⊓
        (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom ⁻¹ᵁ U := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let j : A.left ≅ A.left := ⟨((𝟙 A : A ⟶ A)⁻¹).left,
    ((𝟙 A : A ⟶ A)⁻¹).left, LineBundleSymmetrization.Construction.groupInversion_comp_self A, LineBundleSymmetrization.Construction.groupInversion_comp_self A⟩
  let t := AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b
  let V := t.hom ⁻¹ᵁ U
  let W := (j ≪≫ t).hom ⁻¹ᵁ U
  have hpre (e : A.left ≅ A.left) : ((e.hom ⁻¹ᵁ U : A.left.Opens) : Set A.left).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨e.inv x, by change e.hom (e.inv x) ∈ U; rw [Scheme.inv_hom_apply]; exact hx⟩
  have hVW : ((V ⊓ W : A.left.Opens) : Set A.left).Nonempty :=
    nonempty_preirreducible_inter V.isOpen W.isOpen (hpre t) (hpre (j ≪≫ t))
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hVW (V ⊓ W).isOpen.isLocallyClosed
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hxc) (pointOfClosedPoint_comp A.hom x hxc)
  have ha : a.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply A.hom x hxc _
  have hi : a.left ≫ j.hom = a⁻¹.left := by
    exact congrArg Over.Hom.left
      ((GrpObj.comp_inv a (𝟙 A)).trans (congrArg Inv.inv (Category.comp_id a)))
  refine ⟨a, ?_, ?_⟩
  · have he := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
      (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A b a)
    change (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom
      (b.left (IsLocalRing.closedPoint K)) ∈ U
    exact (congrArg (fun z : A.left => z ∈ U) he).mpr
      ((congrArg (fun z : A.left => t.hom z ∈ U) ha).mpr hx.1)
  · have he : b.left ≫ (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom =
        a.left ≫ (j ≪≫ t).hom := by
      rw [AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A b a⁻¹, ← hi, Category.assoc]
      rfl
    have hv := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K)) he
    change (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom
      (b.left (IsLocalRing.closedPoint K)) ∈ U
    exact (congrArg (fun z : A.left => z ∈ U) hv).mpr
      ((congrArg (fun z : A.left => (j ≪≫ t).hom z ∈ U) ha).mpr hx.2)

theorem exists_opposite_translate_neighborhood
    (U : A.left.Opens) (hU : (U : Set A.left).Nonempty) (x : A.left) :
    ∃ a : 𝟙_ (Over (Spec (.of K))) ⟶ A,
      x ∈ (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom ⁻¹ᵁ U ⊓
        (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom ⁻¹ᵁ U := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure
    isClosed_closure.isLocallyClosed
  let b : 𝟙_ (Over (Spec (.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hyc) (pointOfClosedPoint_comp A.hom y hyc)
  obtain ⟨a, ha⟩ := exists_opposite_translate_rational A U hU b
  have hb : b.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hyc _
  rw [hb] at ha
  exact ⟨a, (specializes_iff_mem_closure.mpr hy).mem_open
    ((AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom ⁻¹ᵁ U ⊓
      (AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a⁻¹).hom ⁻¹ᵁ U).isOpen ha⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OppositeTranslationNeighborhood.Construction
