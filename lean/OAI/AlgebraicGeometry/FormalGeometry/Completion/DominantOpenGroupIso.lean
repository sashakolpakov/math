import OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupPoints
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Dominant Open Group Iso -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupIso

noncomputable section

/-! A dominant open immersion of finite-type algebraic groups is an
isomorphism: its closed complement would have a missing rational point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
  [LocallyOfFiniteType B.hom]
  (f : A ⟶ B) [IsMonHom f] [IsOpenImmersion f.left] [IsDominant f.left]

theorem dominantOpen_groupHom_surjective : Surjective f.left := by
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  constructor
  intro y
  by_contra hy
  have hnonempty : (Set.range f.left)ᶜ.Nonempty := ⟨y, hy⟩
  obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints hnonempty
    f.left.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
  let b : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
    Over.homMk (pointOfClosedPoint B.hom w hwc) (pointOfClosedPoint_comp B.hom w hwc)
  obtain ⟨a, ha⟩ := DominantOpenGroupPoints.Construction.dominantOpen_groupHom_point_surjective f b
  apply hw
  refine ⟨a.left (IsLocalRing.closedPoint K), ?_⟩
  have h := congrArg (fun z : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B =>
    z.left (IsLocalRing.closedPoint K)) ha
  exact h.trans (pointOfClosedPoint_apply B.hom w hwc _)

theorem dominantOpen_groupHom_isIso : IsIso f.left := by
  have := dominantOpen_groupHom_surjective f
  exact (isIso_iff_isOpenImmersion_and_surjective f.left).mpr ⟨inferInstance, inferInstance⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DominantOpenGroupIso
