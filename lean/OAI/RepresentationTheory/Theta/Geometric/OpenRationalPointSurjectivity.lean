import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Open Rational Point Surjectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenRationalPointSurjectivity

noncomputable section

/-! For schemes locally of finite type over an algebraically closed
field, an open image containing every rational point is the whole scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (.of K))} [LocallyOfFiniteType Y.hom]

theorem surjective_of_open_of_rationalPoints (f : X ⟶ Y)
    (hopen : IsOpen (Set.range f.left))
    (hpts : ∀ y : Over.mk (𝟙 (Spec (.of K))) ⟶ Y,
      ∃ x : Over.mk (𝟙 (Spec (.of K))) ⟶ X, x ≫ f = y) : Surjective f.left := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hc : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let p : Over.mk (𝟙 (Spec (.of K))) ⟶ Y :=
      Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
    obtain ⟨x, hx⟩ := hpts p
    refine ⟨x.left (IsLocalRing.closedPoint K), ?_⟩
    have he := congrArg (fun v => v (IsLocalRing.closedPoint K)) (congrArg Over.Hom.left hx)
    exact he.trans (pointOfClosedPoint_apply Y.hom y hy _)
  constructor
  intro y
  by_contra hy
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := (Set.range f.left)ᶜ) ⟨y, hy⟩ hopen.isClosed_compl.isLocallyClosed
  exact hz (hc hzc)

theorem isIso_of_flat_mono_of_rationalPoints (f : X ⟶ Y)
    [Flat f.left] [LocallyOfFinitePresentation f.left] [QuasiCompact f.left] [Mono f.left]
    (hpts : ∀ y : Over.mk (𝟙 (Spec (.of K))) ⟶ Y,
      ∃ x : Over.mk (𝟙 (Spec (.of K))) ⟶ X, x ≫ f = y) : IsIso f.left := by
  have : Surjective f.left := surjective_of_open_of_rationalPoints f
    f.left.isOpenMap.isOpen_range hpts
  exact Flat.isIso_of_surjective_of_mono f.left

end

end OAI.RepresentationTheory.Theta.Geometric.OpenRationalPointSurjectivity
