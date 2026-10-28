import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PolarizationOpenCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GraphPowerZariskiLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiFiniteQuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EnhancementParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GraphPowerEnhancementUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementTransportIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementNormalization

/-! # Global Graph Power Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus

noncomputable section

section

/-! The actual global parameter for zero-normalized powers of the
canonical embedding line of a fixed projective full-level family.
Its affine charts are the constructed rational polarization loci.
Genuine membership descent identifies their gluing with the original
all-test enhancement predicate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)

def subfunctor (d : ℕ) (δ : Fin g → ℕ) : Subfunctor (yoneda.obj M) :=
  GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor M δ F (F.abelian.zeroNormalizedBundle P.ampleLineBundle) d

variable (qS : M.left ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

local instance chart_noetherian (i : M.left.affineOpenCover.I₀) :
    IsNoetherianRing (M.left.affineOpenCover.X i) := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian M.left i

omit [IsNoetherianRing R] [AlgebraicGeometry.IsNoetherian M.left] in
theorem chartLine_isAmple (i : M.left.affineOpenCover.I₀) :
    (P.ampleLineBundle.pullback
      (pullback.fst F.abelian.scheme.hom (M.left.affineOpenCover.f i))).IsAmple :=
  (P.baseChange (M.left.affineOpenCover.f i)).ampleLineBundle_isAmple.of_iso
    (P.baseChangeTwistingBundleIso (M.left.affineOpenCover.f i))

def chart (i : M.left.affineOpenCover.I₀) :
    SubfunctorOpen.SubfunctorOpenChart (subfunctor M F P d δ) (M.left.affineOpenCover.f i) :=
  @PolarizationOpenCharts.rationalNormalizedGraphPowerOpenChart (Spec (.of R)) M g N F P P.ampleLineBundle qS d hd δ hδ
    (M.left.affineOpenCover.X i) (M.left.affineOpenCover.X i).commRing (chart_noetherian M i)
    (M.left.affineOpenCover.f i) (chartLine_isAmple M F P i)

omit [IsNoetherianRing R] in
include qS hd hδ in
theorem localMembership : SubfunctorOpen.SubfunctorZariskiLocalMembership (subfunctor M F P d δ) :=
  GraphPowerZariskiLocality.rationalNormalizedGraphPower_zariskiLocalMembership M F P P.ampleLineBundle qS d hd δ hδ

/-- The parameter over the fixed family base. -/
def relativeParameter : Over M.left :=
  SubfunctorOpen.SubfunctorOpenGluing.parameter (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ)

/-- The same actual parameter over the original affine base. -/
def parameter : Over (Spec (.of R)) :=
  (Over.map M.hom).obj (relativeParameter M F P qS d hd δ hδ)

def inclusion : RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ ⟶ M :=
  CompositeParameterPoints.compositeParameterProjection M (relativeParameter M F P qS d hd δ hδ)

instance relativeParameter_mono : Mono (relativeParameter M F P qS d hd δ hδ).hom :=
  SubfunctorOpen.SubfunctorOpenGluing.parameter_mono (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ)

instance relativeParameter_locallyOfFiniteType :
    LocallyOfFiniteType (relativeParameter M F P qS d hd δ hδ).hom :=
  SubfunctorOpen.SubfunctorOpenGluing.parameter_locallyOfFiniteType (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ)

instance relativeParameter_quasiCompact :
    QuasiCompact (relativeParameter M F P qS d hd δ hδ).hom :=
  SubfunctorOpen.SubfunctorOpenGluing.parameter_quasiCompact (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ)

instance inclusion_left_mono : Mono (inclusion M F P qS d hd δ hδ).left :=
  inferInstanceAs (Mono (relativeParameter M F P qS d hd δ hδ).hom)

instance inclusion_mono : Mono (inclusion M F P qS d hd δ hδ) := Over.mono_of_mono_left _

instance inclusion_locallyOfFiniteType :
    LocallyOfFiniteType (inclusion M F P qS d hd δ hδ).left :=
  inferInstanceAs (LocallyOfFiniteType (relativeParameter M F P qS d hd δ hδ).hom)

instance inclusion_quasiCompact : QuasiCompact (inclusion M F P qS d hd δ hδ).left :=
  inferInstanceAs (QuasiCompact (relativeParameter M F P qS d hd δ hδ).hom)

instance parameter_noetherian : IsNoetherian (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ).left := by
  let : IsLocallyNoetherian (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ).left :=
    SubfunctorOpen.SubfunctorOpenGluing.parameter_locallyNoetherian (subfunctor M F P d δ)
      (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
      (chart M F P qS d hd δ hδ)
  let : CompactSpace (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ).left :=
    SubfunctorOpen.SubfunctorOpenGluing.parameter_compactSpace (subfunctor M F P d δ)
      (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
      (chart M F P qS d hd δ hδ)
  exact ⟨⟩

/-- Recover each constructed affine chart by its actual Cartesian square. -/
def chartMap (i : M.left.affineOpenCover.I₀) :
    (chart M F P qS d hd δ hδ i).parameter.left ⟶ (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ).left :=
  SubfunctorOpen.SubfunctorOpenGluing.chartMap (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ) i

omit [IsNoetherianRing R] in
theorem chart_isPullback (i : M.left.affineOpenCover.I₀) :
    IsPullback (chartMap M F P qS d hd δ hδ i) (chart M F P qS d hd δ hδ i).parameter.hom
      (inclusion M F P qS d hd δ hδ).left (M.left.affineOpenCover.f i) :=
  SubfunctorOpen.SubfunctorOpenGluing.chart_isPullback (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ) i

omit [IsNoetherianRing R] in
/-- Factorization is exactly original enhancement existence on every test scheme. -/
theorem lifts_iff (T : Over (Spec (.of R))) (x : T ⟶ M) :
    (∃ z : T ⟶ RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ,
      z ≫ inclusion M F P qS d hd δ hδ = x) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
        ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
          (pullback.fst F.abelian.scheme.hom x.left)) d) :=
  (SubfunctorOpen.SubfunctorOpenGluing.lifts_iff (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ) T x).symm

omit [IsNoetherianRing R] in
/-- A natural representation of the original subfunctor, over its original inclusion. -/
theorem represents :
    ∃ e : yoneda.obj (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ) ≅ (subfunctor M F P d δ).toFunctor,
      e.hom ≫ (subfunctor M F P d δ).ι = yoneda.map (inclusion M F P qS d hd δ hδ) :=
  SubfunctorOpen.SubfunctorOpenGluing.represents (subfunctor M F P d δ)
    (localMembership M F P qS d hd δ hδ) M.left.affineOpenCover.openCover
    (chart M F P qS d hd δ hδ)

/-- A supplied quasi-projective presentation of the fixed family base
induces one of the constructed parameter over the same affine base. -/
def quasiProjectivePresentation (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ) :=
  Q.monomorphismSource (inclusion M F P qS d hd δ hδ)

/-- The universal point has an actual original polarization enhancement. -/
def universalEnhancement :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      (F.pullback (inclusion M F P qS d hd δ hδ).left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (inclusion M F P qS d hd δ hδ).left)) d :=
  ((lifts_iff M F P qS d hd δ hδ (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ)
    (inclusion M F P qS d hd δ hδ)).mp
      ⟨𝟙 _, Category.id_comp _⟩).some

/-- The universal original polarized abelian scheme, retaining the given full level. -/
def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N (RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ).left :=
  (universalEnhancement M F P qS d hd δ hδ).object

omit [IsNoetherianRing R] in
theorem universalFamily_abelian :
    (universalFamily M F P qS d hd δ hδ).abelian =
      F.abelian.pullback (inclusion M F P qS d hd δ hδ).left := rfl

omit [IsNoetherianRing R] in
theorem universalFamily_level :
    (universalFamily M F P qS d hd δ hδ).level =
      F.level.pullback (inclusion M F P qS d hd δ hδ).left := rfl

def universalPowerIso :
    ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst F.abelian.scheme.hom (inclusion M F P qS d hd δ hδ).left)).sheaf ≅
      ((universalFamily M F P qS d hd δ hδ).graphBundle.tensorPower d).sheaf :=
  (universalEnhancement M F P qS d hd δ hδ).powerIso.some

/-- Pulling the universal enhancement retains the native single-pullback family. -/
def enhancementAt {T : Over (Spec (.of R))} (z : T ⟶ RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ) :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      (F.pullback (z ≫ inclusion M F P qS d hd δ hδ).left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (z ≫ inclusion M F P qS d hd δ hδ).left)) d := by
  let c : Over.mk (z ≫ inclusion M F P qS d hd δ hδ).left ⟶
      Over.mk (inclusion M F P qS d hd δ hδ).left := Over.homMk z.left rfl
  exact GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback
    (F := F) (L := F.abelian.zeroNormalizedBundle P.ampleLineBundle)
    (T := Over.mk (inclusion M F P qS d hd δ hδ).left)
    (U := Over.mk (z ≫ inclusion M F P qS d hd δ hδ).left)
    (universalEnhancement M F P qS d hd δ hδ) c

omit [IsNoetherianRing R] in
theorem enhancementAt_class {T : Over (Spec (.of R))} (z : T ⟶ RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ) :
    (enhancementAt M F P qS d hd δ hδ z).object.classOf =
      ((universalFamily M F P qS d hd δ hδ).pullback z.left).classOf := by
  let c : Over.mk (z ≫ inclusion M F P qS d hd δ hδ).left ⟶
      Over.mk (inclusion M F P qS d hd δ hδ).left := Over.homMk z.left rfl
  exact GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback_object_class
    (F := F) (L := F.abelian.zeroNormalizedBundle P.ampleLineBundle)
    (T := Over.mk (inclusion M F P qS d hd δ hδ).left)
    (U := Over.mk (z ≫ inclusion M F P qS d hd δ hδ).left)
    (universalEnhancement M F P qS d hd δ hδ) c

omit [IsNoetherianRing R] in
/-- Every compatible enhancement above a represented point has the
complete original moduli class of the pulled-back universal family. -/
theorem universalFamily_classifies {T : Over (Spec (.of R))}
    (z : T ⟶ RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ)
    (H : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      (F.pullback (z ≫ inclusion M F P qS d hd δ hδ).left)
      ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
        (pullback.fst F.abelian.scheme.hom (z ≫ inclusion M F P qS d hd δ hδ).left)) d) :
    ((universalFamily M F P qS d hd δ hδ).pullback z.left).classOf = H.object.classOf := by
  apply (enhancementAt_class M F P qS d hd δ hδ z).symm.trans
  exact Universal.GraphPowerEnhancementUniqueness.universalGraphPowerEnhancement_class_unique F.abelian P
    (Over.mk (z ≫ inclusion M F P qS d hd δ hδ).left)
    (F.level.pullback (z ≫ inclusion M F P qS d hd δ hδ).left)
    ((F.abelian.zeroNormalizedBundle P.ampleLineBundle).pullback
      (pullback.fst F.abelian.scheme.hom (z ≫ inclusion M F P qS d hd δ hδ).left))
    d (enhancementAt M F P qS d hd δ hδ z) H hδ hd

end

/-! An original polarized family with a recovered full-level projective
fiber lifts to the represented graph-power locus. The lifted universal
family recovers the complete original moduli object on every test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem transportEnhancement_class
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    {F G : Level.Data.AbelianSchemeWithFullLevel g N S}
    {L : Line.Bundles.LineBundle F.abelian.scheme.left} {M : Line.Bundles.LineBundle G.abelian.scheme.left} {d : ℕ}
    (D : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d)
    (e : F.abelian.scheme ≅ G.abelian.scheme) [IsMonHom e.hom]
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L)
    (hl : F.level.transport e = G.level) :
    D.object.classOf = (D.transportFamily (G := G) e he).object.classOf :=
  (D.object.classOf_eq_iff _).mpr ⟨D.transportFamilyModuliIso (G := G) e he hl⟩

variable {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (qS : M.left ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

omit [IsNoetherianRing R] in
theorem exists_point_recovery {T : Over (Spec (.of R))} (x : T ⟶ M)
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (e : A.abelian.scheme ≅ (F.abelian.pullback x.left).scheme) [IsMonHom e.hom]
    (hl : A.level.transport e = F.level.pullback x.left)
    (hpower : (((P.baseChange x.left).ampleLineBundle).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower d).sheaf) :
    ∃ z : T ⟶ RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ,
      z ≫ inclusion M F P qS d hd δ hδ = x ∧
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A ((universalFamily M F P qS d hd δ hδ).pullback z.left)) := by
  let F₀ : Level.Data.AbelianSchemeWithFullLevel g N T.left := ⟨A.abelian, A.level⟩
  let H₀ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F₀ (A.graphBundle.tensorPower d) d :=
    ⟨A.dual, A.polarization, ⟨Iso.refl _⟩⟩
  let e₀ : F₀.abelian.scheme ≅ (F.pullback x.left).abelian.scheme := e
  let : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e.hom)
  have hl₀ : F₀.level.transport e₀ = (F.pullback x.left).level := hl
  have h₀ : H₀.object = A := rfl
  have he : Line.Bundles.LineBundle.pullbackClass e.hom.left
      (Line.Bundles.LineBundle.classOf (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left))) =
        Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower d) :=
    Quotient.sound ⟨(Scheme.Modules.pullback e.hom.left).mapIso
      (P.baseChangeTwistingBundleIso x.left).symm ≪≫ hpower⟩
  let H₁ : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback x.left)
      (P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) d :=
    H₀.transportFamily (F := F₀) (G := F.pullback x.left)
      (M := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) e₀ he
  have h₁ : H₀.object.classOf = H₁.object.classOf :=
    transportEnhancement_class (F := F₀) (G := F.pullback x.left)
      (M := P.ampleLineBundle.pullback (pullback.fst F.abelian.scheme.hom x.left)) H₀ e₀ he hl₀
  let H := GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter
    (F := F) (L := P.ampleLineBundle) x.left H₁
  have hnorm : H.object = H₁.object :=
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter_object
      (F := F) (L := P.ampleLineBundle) x.left H₁
  have hA : A.classOf = H.object.classOf :=
    (congrArg (fun B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left => B.classOf) h₀).symm.trans
      (h₁.trans (congrArg
        (fun B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left => B.classOf) hnorm).symm)
  obtain ⟨z, hz⟩ := (lifts_iff M F P qS d hd δ hδ T x).mpr ⟨H⟩
  have hclass := universalFamily_classifies M F P qS d hd δ hδ z
  rw [hz] at hclass
  exact ⟨z, hz, (A.classOf_eq_iff ((universalFamily M F P qS d hd δ hδ).pullback z.left)).mp
    (hA.trans (hclass H).symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus
