import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Projective Closure Is -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

noncomputable section

/-!
# RiemannProjectivity: the actual reduced projective closure

The closed scheme is constructed from the vanishing ideal sheaf of the
Zariski closure of the embedded complex points. It is reduced and genuinely
projective over ℂ. Every original complex point lifts to that scheme.
Equality of its complex points with the analytic image is a separate theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set

variable {n : ℕ}

def underlyingPoint (p : Projectivization ℂ (Fin (n + 1) → ℂ)) : OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n :=
  (OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left (IsLocalRing.closedPoint ℂ)

def closureSupport (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    Closeds (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := .closure (underlyingPoint '' S)

def closureIdeal (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (closureSupport S)

def closureScheme (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) : Scheme :=
  (closureIdeal S).subscheme

def closureInclusion (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    closureScheme S ⟶ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n := (closureIdeal S).subschemeι

instance (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    IsClosedImmersion (closureInclusion S) :=
  inferInstanceAs (IsClosedImmersion (closureIdeal S).subschemeι)

def closureStructureMap (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    closureScheme S ⟶ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := closureInclusion S ≫ OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n

def closurePresentation (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (closureScheme S) (closureStructureMap S) :=
  ⟨n, closureInclusion S, inferInstance, rfl⟩

instance closureScheme_reduced (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    IsReduced (closureScheme S) := by
  let I := closureIdeal S
  change IsReduced I.subscheme
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  intro U
  change (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n).affineOpens at U
  change IsReduced (Spec (.of (Γ(OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, U) ⧸ I.ideal U)))
  apply (affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance closureStructureMap_proper (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    IsProper (closureStructureMap S) := (closurePresentation S).isProper

theorem inclusion_range (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    range (closureInclusion S) = (closureSupport S : Set (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  change range (closureIdeal S).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [closureIdeal]

theorem underlying_mem_support (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    {p : Projectivization ℂ (Fin (n + 1) → ℂ)} (hp : p ∈ S) :
    underlyingPoint p ∈ closureSupport S :=
  subset_closure ⟨p, hp, rfl⟩

def closureOver (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) : Over OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (closureStructureMap S)

def inclusionOver (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    closureOver S ⟶ Over.mk (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  Over.homMk (closureInclusion S) rfl

/-- An original complex point lies on the actual reduced closure scheme. -/
theorem exists_liftedPoint (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : underlyingPoint p ∈ closureSupport S) :
    ∃ q : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (closureOver S),
      OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (inclusionOver S) q = OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p := by
  let : LocallyOfFiniteType (closureStructureMap S) := (closurePresentation S).finiteType.1
  have hp' : underlyingPoint p ∈ range (closureInclusion S) := by
    rw [inclusion_range]
    exact hp
  obtain ⟨x, hx⟩ := hp'
  let P := OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p
  have hpc : IsClosed ({underlyingPoint p} : Set (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :=
    (pointEquivClosedPoint (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) ⟨P.left, P.w⟩).property
  have hxc : IsClosed ({x} : Set (closureScheme S)) := by
    have h := hpc.preimage (closureInclusion S).continuous
    convert! h using 1
    ext y
    simp only [mem_singleton_iff, mem_preimage]
    rw [← hx]
    exact (closureInclusion S).isClosedEmbedding.injective.eq_iff.symm
  let q₀ : OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ closureScheme S :=
    pointOfClosedPoint (X := closureScheme S) (K := ℂ) (closureStructureMap S) x hxc
  have hq₀ : q₀ ≫ closureStructureMap S = 𝟙 OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
    pointOfClosedPoint_comp (closureStructureMap S) x hxc
  let q : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (closureOver S) := Over.homMk q₀ hq₀
  refine ⟨q, ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq (OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (inclusionOver S) q).w P.w
  change closureInclusion S
    ((pointOfClosedPoint (closureStructureMap S) x hxc) (IsLocalRing.closedPoint ℂ)) = underlyingPoint p
  exact (congrArg (closureInclusion S)
    (pointOfClosedPoint_apply (closureStructureMap S) x hxc (IsLocalRing.closedPoint ℂ))).trans hx

def liftedPoint (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : underlyingPoint p ∈ closureSupport S) : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (closureOver S) :=
  Classical.choose (exists_liftedPoint S p hp)

theorem liftedPoint_inclusion (S : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : underlyingPoint p ∈ closureSupport S) :
    OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (inclusionOver S) (liftedPoint S p hp) =
      OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p :=
  Classical.choose_spec (exists_liftedPoint S p hp)

variable {T : Type} [TopologicalSpace T]

/-- Lift the entire parametrized image through the genuine closed immersion. -/
def liftedMap (f : T → Projectivization ℂ (Fin (n + 1) → ℂ)) :
    T → OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (closureOver (range f)) :=
  fun t => liftedPoint (range f) (f t) (underlying_mem_support (range f) ⟨t, rfl⟩)

omit [TopologicalSpace T] in
theorem liftedMap_inclusion (f : T → Projectivization ℂ (Fin (n + 1) → ℂ)) (t : T) :
    OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (inclusionOver (range f)) (liftedMap f t) =
      OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) :=
  liftedPoint_inclusion (range f) (f t) _

theorem liftedMap_continuous (f : T → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Continuous f) : Continuous (liftedMap f) := by
  let j := inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (closureInclusion (range f)))
  have hj := OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion j
  apply hj.isEmbedding.isInducing.continuous_iff.mpr
  have heq : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j ∘ liftedMap f =
      OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n ∘ f :=
    funext (liftedMap_inclusion f)
  rw [heq]
  exact (OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).continuous.comp hf

omit [TopologicalSpace T] in
theorem liftedMap_injective (f : T → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Function.Injective f) : Function.Injective (liftedMap f) := by
  intro x y hxy
  apply hf
  apply (OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).injective
  exact (liftedMap_inclusion f x).symm.trans
    ((congrArg (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (inclusionOver (range f))) hxy).trans
      (liftedMap_inclusion f y))

/-- A compact embedded analytic image lifts as a closed topological embedding
into the actual complex points of its reduced projective closure. -/
theorem liftedMap_isClosedEmbedding [CompactSpace T]
    (f : T → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Topology.IsClosedEmbedding f) : Topology.IsClosedEmbedding (liftedMap f) := by
  let j := inclusionOver (range f)
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (closureInclusion (range f)))
  let : T2Space (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (closureOver (range f))) :=
    (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion j).isEmbedding.t2Space
  exact (liftedMap_continuous f hf.continuous).isClosedEmbedding (liftedMap_injective f hf.injective)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure
