import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitComponents
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Component Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Actual component data, projective presentations and coproduct
decompositions survive arithmetic base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def ComponentBaseChange.relativeProjectivePresentationBaseChange {B C : Scheme} (g : C ⟶ B)
    {X : Over B} (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation ((Over.pullback g).obj X) := by
  let F := Over.pullback g
  let e := AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso g P.dimension
  have : IsClosedImmersion (F.map P.embedding).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square g P.embedding) P.closedImmersion
  have : IsIso e.inv.left := ((Over.forget C).mapIso e).isIso_inv
  exact ⟨P.dimension, F.map P.embedding ≫ e.inv,
    inferInstanceAs (IsClosedImmersion ((F.map P.embedding).left ≫ e.inv.left))⟩

theorem ComponentBaseChange.relativelyProjective_baseChange {B C : Scheme} (g : C ⟶ B)
    {X : Over B} (hX : Components.RelativelyProjective X) :
    Components.RelativelyProjective ((Over.pullback g).obj X) := by
  obtain ⟨P⟩ := hX
  exact ⟨ComponentBaseChange.relativeProjectivePresentationBaseChange g P⟩

def Components.ComponentAlbaneseData.baseChange {B C : Scheme} (g : C ⟶ B)
    {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r) :
    Components.ComponentAlbaneseData ((Over.pullback g).obj T) r where
  S i := (Over.pullback g).obj (D.S i)
  A i := (Over.pullback g).mapCommGrp.obj (D.A i)
  x₀ i := Section.Comparisons.mappedSection (Over.pullback g) (D.x₀ i)
  a i := (Over.pullback g).map (D.a i)

def ComponentBaseChange.baseChangeDecompositionIso {B C : Scheme} (g : C ⟶ B)
    {r : ℕ} (S : Fin r → Over B) {X : Over B} (e : (∐ S) ≅ X) :
    (∐ fun i => (Over.pullback g).obj (S i)) ≅ (Over.pullback g).obj X := by
  let F := Over.pullback g
  let V (i : Fin r) := F.obj (S i)
  let f (i : Fin r) : V i ⟶ F.obj X := F.map (Sigma.ι S i ≫ e.hom)
  have : ∀ i, IsOpenImmersion (f i).left := by
    intro i
    have : IsOpenImmersion (Sigma.ι S i ≫ e.hom).left := Coproduct.decomposition_inclusion_open S e i
    exact Coproduct.baseChange_inclusion_open g _
  have hc : (⋃ i, Set.range (f i).left) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr (Coproduct.baseChange_decomposition_cover S g e x)
  let q := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f
  have : IsIso q.left := DisjointOpenCoverFinite.disjoint_open_cover_sigma_isIso
    (fun i => (V i).left) (fun i => (f i).left) (Coproduct.baseChange_decomposition_disjoint S g e) hc
  exact SplitComponents.overCoproductIsoSigma V ≪≫ Over.isoMk (asIso q.left) q.w

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
