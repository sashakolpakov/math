import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctorCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeParameterPoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Subfunctor Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen

noncomputable section

/-! Glue actual monomorphic chart loci of a relative subfunctor.
Membership descent is an explicit hypothesis: local representability alone
does not identify the presheaf with the sheaf represented by the gluing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {B : Scheme.{u}} {M : Over B}

/-- Membership in the original subfunctor descends from a covering sieve. -/
def SubfunctorZariskiLocalMembership (F : Subfunctor (yoneda.obj M)) : Prop :=
  ∀ (T : Over B) (x : T ⟶ M),
    F.sieveOfSection x ∈ (Scheme.zariskiTopology.over B) T → x ∈ F.obj (.op T)

theorem subfunctor_isSheaf_of_zariskiLocalMembership
    (F : Subfunctor (yoneda.obj M)) (hF : SubfunctorZariskiLocalMembership F) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over B) F.toFunctor := by
  have hM := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.zariskiTopology.over B) (yoneda.obj M)
  apply (F.isSheaf_iff hM).mpr
  intro T x hx
  exact hF T.unop x hx

/-- An actual chart parameter, with the original all-test factorization
criterion. The chart hypotheses concern only the supplied local locus. -/
structure SubfunctorOpenChart (F : Subfunctor (yoneda.obj M))
    {U : Scheme.{u}} (i : U ⟶ M.left) where
  parameter : Over U
  mono : Mono parameter.hom
  locallyFiniteType : LocallyOfFiniteType parameter.hom
  quasiCompact : QuasiCompact parameter.hom
  lifts : ∀ (T : Scheme.{u}) (a : T ⟶ U),
    (a ≫ i) ∈ (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).obj (.op T) ↔
      ∃ z : T ⟶ parameter.left, z ≫ parameter.hom = a

attribute [instance] SubfunctorOpenChart.mono
attribute [instance] SubfunctorOpenChart.locallyFiniteType
attribute [instance] SubfunctorOpenChart.quasiCompact

namespace SubfunctorOpenGluing
variable (F : Subfunctor (yoneda.obj M))
    (hF : SubfunctorZariskiLocalMembership F) (U : M.left.OpenCover.{u})
    (C : ∀ i, SubfunctorOpenChart F (U.f i))

include hF U C in
theorem underlying_isRepresentable : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable :=
  FormalGeometry.Completion.SubfunctorSchemeGluing.Construction.subfunctor_isRepresentable_of_openCover (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F) U
    (fun i => (C i).parameter) (fun i => (C i).lifts)
    (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor_isSheaf F Scheme.zariskiTopology
      (subfunctor_isSheaf_of_zariskiLocalMembership F hF))

/-- The scheme obtained by gluing the original chart loci over the parameter base. -/
def parameter : Over M.left := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  exact FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctorFamily (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F)

instance parameter_mono : Mono (SubfunctorOpenGluing.parameter F hF U C).hom := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  exact FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctorFamily_mono (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F)

/-- Every chart is recovered by its actual Cartesian square. -/
def chartMap (i : U.I₀) : (C i).parameter.left ⟶ (SubfunctorOpenGluing.parameter F hF U C).left := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  exact FormalGeometry.Completion.RepresentedSubfunctorCharts.Construction.representedSubfunctorChartMap (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F) (U.f i)
    (C i).parameter.hom (C i).lifts

theorem chart_isPullback (i : U.I₀) :
    IsPullback (chartMap F hF U C i) (C i).parameter.hom (SubfunctorOpenGluing.parameter F hF U C).hom (U.f i) := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  exact FormalGeometry.Completion.RepresentedSubfunctorCharts.Construction.representedSubfunctorChart_isPullback (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F) (U.f i)
    (C i).parameter.hom (C i).lifts

theorem parameter_localProperty (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ i, Q (C i).parameter.hom) : Q (SubfunctorOpenGluing.parameter F hF U C).hom := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  exact FormalGeometry.Completion.RepresentedSubfunctorCharts.Construction.representedSubfunctor_localProperty (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F) U
    (fun i => (C i).parameter) (fun i => (C i).lifts) Q hQ

instance parameter_locallyOfFiniteType : LocallyOfFiniteType (SubfunctorOpenGluing.parameter F hF U C).hom := by
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  exact parameter_localProperty F hF U C (@LocallyOfFiniteType) (fun i => (C i).locallyFiniteType)

instance parameter_quasiCompact : QuasiCompact (SubfunctorOpenGluing.parameter F hF U C).hom := by
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  exact parameter_localProperty F hF U C (@QuasiCompact) (fun i => (C i).quasiCompact)

instance parameter_locallyNoetherian [IsLocallyNoetherian M.left] :
    IsLocallyNoetherian (SubfunctorOpenGluing.parameter F hF U C).left :=
  LocallyOfFiniteType.isLocallyNoetherian (SubfunctorOpenGluing.parameter F hF U C).hom

instance parameter_compactSpace [CompactSpace M.left] : CompactSpace (SubfunctorOpenGluing.parameter F hF U C).left :=
  QuasiCompact.compactSpace_of_compactSpace (SubfunctorOpenGluing.parameter F hF U C).hom

/-- Retain the original ambient base. -/
def parameterOver : Over B := (Over.map M.hom).obj (SubfunctorOpenGluing.parameter F hF U C)

def inclusion : parameterOver F hF U C ⟶ M :=
  CompositeParameterPoints.compositeParameterProjection M (SubfunctorOpenGluing.parameter F hF U C)

instance inclusion_mono : Mono (inclusion F hF U C) := by
  let : Mono (inclusion F hF U C).left := parameter_mono F hF U C
  exact Over.mono_of_mono_left _

instance inclusion_locallyOfFiniteType : LocallyOfFiniteType (inclusion F hF U C).left :=
  parameter_locallyOfFiniteType F hF U C

instance inclusion_quasiCompact : QuasiCompact (inclusion F hF U C).left :=
  parameter_quasiCompact F hF U C

/-- The original predicate is equivalent to factorization, on every test scheme. -/
theorem lifts_iff (T : Over B) (x : T ⟶ M) :
    x ∈ F.obj (.op T) ↔ ∃ z : T ⟶ parameterOver F hF U C, z ≫ inclusion F hF U C = x := by
  let : (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F).toFunctor.IsRepresentable := underlying_isRepresentable F hF U C
  have hp := FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor_mem F x
  have hf := FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctor_factorization (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F) T.left x.left
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := hf.mp (hp.mpr hx)
    have hw : z ≫ (parameterOver F hF U C).hom = T.hom := by
      change z ≫ ((SubfunctorOpenGluing.parameter F hF U C).hom ≫ M.hom) = T.hom
      exact (Category.assoc z (FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctorFamily (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor F)).hom M.hom).symm.trans
        ((congrArg (fun a => a ≫ M.hom) hz).trans x.w)
    exact ⟨Over.homMk z hw, Over.OverMorphism.ext hz⟩
  · rintro ⟨z, hz⟩
    exact hp.mp (hf.mpr ⟨z.left, congrArg Over.Hom.left hz⟩)

theorem represents :
    ∃ e : yoneda.obj (parameterOver F hF U C) ≅ F.toFunctor,
      e.hom ≫ F.ι = yoneda.map (inclusion F hF U C) :=
  HilbertScheme.Presentations.SubfunctorRepresentations.subfunctor_representation_of_lifts F (inclusion F hF U C)
    (lifts_iff F hF U C)

end SubfunctorOpenGluing

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubfunctorOpen
