import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf

/-! # Paired Translate Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedTranslateCover.CM

noncomputable section

/-! Opposite translates of one nonempty affine open give affine
neighborhoods covering the original proper connected commutative group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

local notation "Point" => 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A

def pairedOpen (U : A.left.Opens) (b : Point) : A.left.Opens :=
  (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom ⁻¹ᵁ U ⊓
    (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom ⁻¹ᵁ U

omit [IsAlgClosed K] in
theorem affine [A.left.IsSeparated] (U : A.left.Opens) (hU : IsAffineOpen U) (b : Point) :
    IsAffineOpen (pairedOpen A U b) :=
  (hU.preimage_of_isIso _).inf (hU.preimage_of_isIso _)

theorem closed_point_covered [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    (U : A.left.Opens) (hne : (U : Set A.left).Nonempty)
    (x : A.left) (hx : IsClosed {x}) : ∃ b : Point, x ∈ pairedOpen A U b := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let a : Point := Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let V : A.left.Opens := (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom ⁻¹ᵁ U
  let invIso : A.left ≅ A.left :=
    (Over.forget (Spec (.of K))).mapIso (asIso (GrpObj.inv (X := A)))
  let W : A.left.Opens := invIso.hom ⁻¹ᵁ V
  have hV : (V : Set A.left).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    refine ⟨(Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).inv z, ?_⟩
    change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom
      ((Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).inv z) ∈ U
    rwa [Scheme.inv_hom_apply]
  have hW : (W : Set A.left).Nonempty := by
    obtain ⟨z, hz⟩ := hV
    refine ⟨invIso.inv z, ?_⟩
    change invIso.hom (invIso.inv z) ∈ V
    rwa [Scheme.inv_hom_apply]
  have hVW : ((V ⊓ W : A.left.Opens) : Set A.left).Nonempty :=
    nonempty_preirreducible_inter V.isOpen W.isOpen hV hW
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hVW (V ⊓ W).isOpen.isLocallyClosed
  let b : Point := Over.homMk (pointOfClosedPoint A.hom z hzc) (pointOfClosedPoint_comp A.hom z hzc)
  have ha : a.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply A.hom x hx _
  have hb : b.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply A.hom z hzc _
  have hbi : (b⁻¹).left (IsLocalRing.closedPoint K) = invIso.hom z := by
    change (GrpObj.inv (X := A)).left (b.left (IsLocalRing.closedPoint K)) = invIso.hom z
    rw [hb]
    rfl
  have exchange (c : Point) :
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A c).hom x =
        (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (c.left (IsLocalRing.closedPoint K)) := by
    have h := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.exchange A a c)
    change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A c).hom (a.left (IsLocalRing.closedPoint K)) =
      (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A a).hom (c.left (IsLocalRing.closedPoint K)) at h
    exact (congrArg (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A c).hom ha).symm.trans h
  refine ⟨b, ?_, ?_⟩
  · change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom x ∈ U
    rw [exchange, hb]
    exact hz.1
  · change (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom x ∈ U
    rw [exchange, hbi]
    exact hz.2

theorem covers [IsProper A.hom] [GeometricallyConnected A.hom]
    (U : A.left.Opens) (hne : (U : Set A.left).Nonempty)
    (x : A.left) : ∃ b : Point, x ∈ pairedOpen A U b := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IrreducibleSpace A.left := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty x).closure
    isClosed_closure.isLocallyClosed
  obtain ⟨b, hb⟩ := closed_point_covered A U hne y hyc
  exact ⟨b, (specializes_iff_mem_closure.mpr hy).mem_open (pairedOpen A U b).isOpen hb⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedTranslateCover.CM
