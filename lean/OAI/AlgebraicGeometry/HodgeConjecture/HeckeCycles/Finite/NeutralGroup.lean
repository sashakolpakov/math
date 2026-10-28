import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition

/-! # Neutral Group -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM

noncomputable section

/-! The neutral factor of the canonical finite group decomposition is a
finite connected group scheme. Its scheme structure is the full kernel
of the point retraction, including all infinitesimal directions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsCommMonObj A.X]

omit [IsCommMonObj A.X] in
theorem pointGroup_finite : IsFinite (GroupDecomposition.CM.pointGroup A).X.hom := by
  let : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) :=
    Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_overPoints A.X (𝟙 _)
  exact AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme_finite (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)

omit [IsCommMonObj A.X] in
theorem componentMap_finite : IsFinite (GroupRetraction.CM.componentMap A).left := by
  let : IsFinite (GroupDecomposition.CM.pointGroup A).X.hom := pointGroup_finite A
  let : IsProper (GroupDecomposition.CM.pointGroup A).X.hom := inferInstance
  let hsep : IsSeparated (GroupDecomposition.CM.pointGroup A).X.hom := inferInstance
  have hcomp : IsFinite ((GroupRetraction.CM.componentMap A).left ≫ (GroupDecomposition.CM.pointGroup A).X.hom) :=
    (congrArg IsFinite (GroupRetraction.CM.componentMap A).w).mpr (inferInstance : IsFinite A.X.hom)
  exact @IsFinite.of_comp _ _ _ (GroupRetraction.CM.componentMap A).left (GroupDecomposition.CM.pointGroup A).X.hom hcomp hsep

omit [IsCommMonObj A.X] in
theorem neutral_finite : IsFinite (GroupDecomposition.CM.neutralPart A).X.hom := by
  let : IsFinite (GroupRetraction.CM.componentMap A).left := componentMap_finite A
  exact Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (GroupRetraction.CM.componentMap A)

theorem neutral_subsingleton : Subsingleton (GroupDecomposition.CM.neutralPart A).X.left := by
  let : IsFinite (GroupDecomposition.CM.neutralPart A).X.hom := neutral_finite A
  constructor
  intro x y
  obtain ⟨p, rfl⟩ := (SchemePoints.CM.pointsEquiv (GroupDecomposition.CM.neutralPart A).X).surjective x
  obtain ⟨q, rfl⟩ := (SchemePoints.CM.pointsEquiv (GroupDecomposition.CM.neutralPart A).X).surjective y
  exact congrArg (SchemePoints.CM.pointsEquiv (GroupDecomposition.CM.neutralPart A).X)
    ((GroupDecomposition.CM.neutral_points_trivial A p).trans (GroupDecomposition.CM.neutral_points_trivial A q).symm)

theorem neutral_connected : ConnectedSpace (GroupDecomposition.CM.neutralPart A).X.left := by
  let : Subsingleton (GroupDecomposition.CM.neutralPart A).X.left := neutral_subsingleton A
  apply connectedSpace_iff_univ.mpr
  refine ⟨⟨(1 : Over.mk (𝟙 (Spec (.of k))) ⟶ (GroupDecomposition.CM.neutralPart A).X).left
    (IsLocalRing.closedPoint k), Set.mem_univ _⟩, ?_⟩
  exact (show (Set.univ : Set (GroupDecomposition.CM.neutralPart A).X.left).Subsingleton from
    fun _ _ _ _ => Subsingleton.elim _ _).isPreconnected

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM
