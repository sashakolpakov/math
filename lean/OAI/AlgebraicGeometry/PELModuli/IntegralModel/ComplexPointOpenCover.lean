import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Complex Point Open Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexPointOpenCover

noncomputable section

/-! For an actual finite-type complex scheme, open images covering all
native complex points cover every scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem complex_point_open_images_cover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    {I : Type} (Y : I → Over Foundations.Scheme.ProjectiveSpace.complexBase) (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i).left]
    (h : ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ i, ∃ q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Y i), q ≫ f i = p) :
    (⋃ i, Set.range (f i).left) = Set.univ := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have ho : IsOpen (⋃ i, Set.range (f i).left) := isOpen_iUnion
    (fun i => (f i).left.isOpenEmbedding.isOpen_range)
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_contra hx
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints
    (X := X.left) (show ((⋃ i, Set.range (f i).left)ᶜ).Nonempty from ⟨x, hx⟩)
    ho.isClosed_compl.isLocallyClosed
  let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := (Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints X.hom).symm ⟨z, hc⟩
  have hp : p.left (IsLocalRing.closedPoint ℂ) = z :=
    congrArg Subtype.val ((Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints X.hom).apply_symm_apply ⟨z, hc⟩)
  obtain ⟨i, q, hq⟩ := h p
  apply hz
  refine Set.mem_iUnion.mpr ⟨i, q.left (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (congrArg (fun a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => a.left (IsLocalRing.closedPoint ℂ)) hq).trans hp

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComplexPointOpenCover
