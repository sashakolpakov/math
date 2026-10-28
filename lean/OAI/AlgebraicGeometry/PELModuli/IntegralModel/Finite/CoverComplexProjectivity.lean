import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverProjectivity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionPresentation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothComponents
import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite

/-! # Cover Complex Projectivity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverComplexProjectivity

noncomputable section

/-! A smooth proper complex target of a finite faithfully flat
projective cover is projective. Its integral components have constructed
Hilbert embeddings, which are assembled in disjoint projective blocks. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem complex_target_projective_of_finite_flat_cover
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    [Smooth Y.hom] [IsProper Y.hom]
    (BX : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) :
    Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  let I := irreducibleComponents Y.left
  have : Finite I := finite_irreducibleComponents_of_isNoetherian.to_subtype
  let U (i : I) := ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen Y.hom i
  let C (i : I) := ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction.overOpen Y (U i)
  let c (i : I) : C i ⟶ Y := ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction.overOpenInclusion Y (U i)
  have hi (i : I) : IsIntegral (C i).left := ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_integral Y.hom i
  have hc (i : I) : IsClosedImmersion (c i).left := ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_closedImmersion Y.hom i
  have hs (i : I) : Smooth (C i).hom := (ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_smooth_proper Y.hom i).1
  have hp (i : I) : IsProper (C i).hom := (ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_smooth_proper Y.hom i).2
  let B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X :=
    Presentations.Parameter.e34ProjectivePresentationOfNative (Classical.choice (Projective.PartitionPresentation.native_projective_relative_presentation BX))
  have hP (i : I) : HilbertScheme.Presentations.Has.Core.IsProjectiveOver (C i) := by
    let Z := pullback q (c i)
    let a : Z ⟶ X := pullback.fst q (c i)
    let b : Z ⟶ C i := pullback.snd q (c i)
    have h := (IsPullback.of_hasPullback q (c i)).map (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase)
    have : IsClosedImmersion a.left := MorphismProperty.of_isPullback h.flip (hc i)
    have : IsFinite b.left := MorphismProperty.of_isPullback h (inferInstanceAs (IsFinite q.left))
    have : Flat b.left := MorphismProperty.of_isPullback h (inferInstanceAs (Flat q.left))
    have : Surjective b.left := MorphismProperty.of_isPullback h (inferInstanceAs (Surjective q.left))
    have : LocallyOfFinitePresentation b.left :=
      MorphismProperty.of_isPullback h (inferInstanceAs (LocallyOfFinitePresentation q.left))
    have : IsIntegral (C i).left := hi i
    have : IsProper (C i).hom := hp i
    exact CoverProjectivity.integral_target_projective_of_finite_flat_cover b (B.precompose a)
  let P (i : I) : Foundations.Scheme.SmoothProjective.ProjectivePresentation (C i).left (C i).hom :=
    AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
      (Presentations.Parameter.nativeProjectivePresentationOfPresentations (Classical.choice (hP i)))
  let V (i : I) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
    ⟨⟨(C i).left, (C i).hom, P i, hs i⟩, hi i⟩
  let f (i : I) : (V i).toOver ⟶ Y := c i
  have : ∀ i, IsOpenImmersion (f i).left := fun i => inferInstanceAs (IsOpenImmersion (U i).ι)
  have hd : Pairwise (fun i j => Disjoint (Set.range (f i).left) (Set.range (f j).left)) := by
    intro i j hij
    change Disjoint (Set.range (U i).ι) (Set.range (U j).ι)
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, Opens.coe_disjoint]
    exact ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_disjoint Y.hom i j hij
  have hcover : (⋃ i, Set.range (f i).left) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy : y ∈ ⨆ i, U i := by rw [ArithmeticGeometry.Models.SpreadingOut.SmoothComponents.Construction.smoothComponentOpen_cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact Set.mem_iUnion.mpr ⟨i, ⟨⟨y, hi⟩, rfl⟩⟩
  have : IsIso (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigmaDesc f).left :=
    DisjointOpenCoverFinite.disjoint_open_cover_sigma_isIso (fun i => (V i).carrier) (fun i => (f i).left) hd hcover
  exact Projective.PartitionPresentation.projective_partition_native_presentation V f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverComplexProjectivity
