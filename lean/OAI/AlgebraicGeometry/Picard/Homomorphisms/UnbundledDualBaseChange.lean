import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange

/-! # Unbundled Dual Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms

noncomputable section

/-! Arbitrary base change of the dimension-independent dual Poincare
representation. The representing property, homogeneous universal class,
and zero-section normalizations are all transported from the original data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

universe u
variable {S S' : Scheme.{u}} {A : Over S} [GrpObj A]

/-- Restriction of the represented presheaf is represented by the base change. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.restrictedRepresentable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    ((Over.map f).op ⋙ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj).RepresentableBy
      (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) where
  homEquiv {T} := ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian) f T).trans
    D.representable.homEquiv
  homEquiv_comp {T U} h a := by
    exact (congrArg D.representable.homEquiv
      ((UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp D.abelian) f h a)).trans
        (D.representable.homEquiv_comp ((Over.map f).map h)
          ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian) f U a))

/-- The base change of the dual represents the homogeneous Picard sheaf
of the base-changed abelian scheme. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.pullbackRepresentable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj.RepresentableBy (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) :=
  (D.restrictedRepresentable f).ofIso
    (((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardSheafBaseChangeIso A) f)).symm)

/-- The representing equivalence after base change preserves the origin. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.pullbackRepresentable_origin (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) (T : Over S') :
    (D.pullbackRepresentable f).homEquiv (1 : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T := by
  apply ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f T).injective
  change (UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f T
    (((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f T).symm
      (D.representable.homEquiv ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian) f T 1))) = _
  rw [Equiv.apply_symm_apply, (UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.trivialHomogeneousPicardClass_baseChange A)]
  exact (congrArg D.representable.homEquiv
    ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv D.abelian) f T).map_one).trans
      (D.origin ((Over.map f).obj T))

/-- The projection from a base change, viewed over the original base. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection (B : Over S) [GrpObj B] (f : S' ⟶ S) :
    (Over.map f).obj (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup B f) ⟶ B :=
  (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B) f (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup B f) (𝟙 _)

/-- The map from the product of the two changed abelian schemes to the old product. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (Over.map f).obj ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ⟶
      D.abelian ⊗ A :=
  ((UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangeFamilyIso A) f (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)).hom ≫
    (UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f ▷ A)

@[reassoc (attr := simp)]
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap_fst (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    D.poincarePullbackOverMap f ≫ fst D.abelian A =
      (Over.map f).map (fst (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ≫
        UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f := by
  rw [UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap, Category.assoc, whiskerRight_fst,
    (UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangeFamilyIso_hom_fst_assoc A)]

@[reassoc (attr := simp)]
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap_snd (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    D.poincarePullbackOverMap f ≫ snd D.abelian A =
      (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
        (snd (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) := by
  rw [UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap, Category.assoc, whiskerRight_snd,
    (UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangeFamilyIso_hom_snd A)]

@[simp]
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection_comp (B : Over S) [GrpObj B] (f : S' ⟶ S)
    {T : Over S'} (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup B f)) :
    (Over.map f).map a ≫ UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection B f = (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B) f T a :=
  ((UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp B) f a (𝟙 _)).symm.trans
    (congrArg ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B) f T) (Category.comp_id a))

@[simp]
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangePointsEquiv_one (B : Over S) [GrpObj B] (f : S' ⟶ S) (T : Over S') :
    (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B) f T 1 = 1 :=
  ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv B) f T).map_one

/-- The Poincare product map respects the zero section in the abelian factor. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap_abelianZero (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (Over.map f).map
        (lift (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
          (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))) ≫
        D.poincarePullbackOverMap f =
      UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f ≫
        lift (𝟙 D.abelian) (1 : D.abelian ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc, ← UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp, UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection]
  · simp [Category.assoc, ← UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp]

/-- The Poincare product map respects the zero section in the dual factor. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackOverMap_dualZero (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (Over.map f).map
        (lift (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
          (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))) ≫ D.poincarePullbackOverMap f =
      UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection A f ≫
        lift (1 : A ⟶ D.abelian) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc, ← UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp]
  · simp [Category.assoc, ← UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp, UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection]

/-- The actual Poincare line bundle after change of base. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (D.poincarePullbackOverMap f).left D.poincare

/-- The pulled-back Poincare class is the restriction of the old universal class. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback_comparison (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app
        (.op (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincarePullback f)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map (UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f).op
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) := by
  let e := AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)
  let c := UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f ▷ A
  exact (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.hom c.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso e).left_inv
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)))

/-- The pulled-back Poincare bundle is homogeneous. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback_homogeneous (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincarePullback f)) := by
  apply ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.isHomogeneousPicardClass_baseChange_iff A) f (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) _).mpr
  exact (congrArg ((UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) ((Over.map f).obj (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)))
    (D.poincarePullback_comparison f)).mpr
      (D.poincareHomogeneous.pullback A (UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f))

/-- The homogeneous presheaf class of the original Poincare bundle. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.poincareRawClass (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (.op D.abelian) :=
  ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩

/-- The homogeneous presheaf class of the pulled-back Poincare bundle. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackRawClass (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) :=
  ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincarePullback f), D.poincarePullback_homogeneous f⟩

/-- Comparison of the Poincare classes in the homogeneous presheaves. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullbackRawClass_comparison (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardPresheafBaseChangeIso A) f).hom.app (.op (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
        (D.poincarePullbackRawClass f) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map (UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f).op D.poincareRawClass :=
  Subtype.ext (D.poincarePullback_comparison f)

/-- Compatibility of the representing bijection with the sheaf comparison. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.pullbackRepresentable_comparison (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) :
    (UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f T ((D.pullbackRepresentable f).homEquiv a) =
      D.representable.homEquiv ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D.abelian) f T a) :=
  ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f T).apply_symm_apply _

/-- The Poincare class remains the universal element after base change. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback_universalClass (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    (D.pullbackRepresentable f).homEquiv (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) =
      (toSheafify (Scheme.fppfTopology.over S') (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))).app
        (.op (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)) (D.poincarePullbackRawClass f) := by
  let c := UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f
  let unitMap := toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)
  apply ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.homogeneousPicardBaseChangeEquiv A) f (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f)).injective
  exact (D.pullbackRepresentable_comparison f _ (𝟙 _)).trans
    ((D.representable.homEquiv_eq c).trans
      ((congrArg ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.map c.op) D.universalClass).trans
        ((unitMap.naturality_apply c.op D.poincareRawClass).symm.trans
          ((congrArg (fun z => unitMap.app (.op ((Over.map f).obj (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))) z)
            (D.poincarePullbackRawClass_comparison f).symm).trans
              ((UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.toHomogeneousPicard_baseChange_apply A) f _ (D.poincarePullbackRawClass f)).symm))))

/-- Normalization at the abelian zero section is preserved by base change. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback_normalizedAtAbelianZero (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (lift (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
        (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))).left
      (D.poincarePullback f)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f).left) := by
  obtain ⟨e⟩ := D.normalizedAtAbelianZero
  let i := lift (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
    (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
  let j := lift (𝟙 D.abelian) (1 : D.abelian ⟶ A)
  let c := UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection D.abelian f
  let p := D.poincarePullbackOverMap f
  have h : i.left ≫ p.left = c.left ≫ j.left :=
    congrArg (fun z : (Over.map f).obj (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f) ⟶
      D.abelian ⊗ A => z.left) (D.poincarePullbackOverMap_abelianZero f)
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp c.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback c.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c.left⟩

/-- Normalization at the dual zero section is preserved by base change. -/
theorem UnbundledDualData.Construction.UnbundledPicard.DualData.poincarePullback_normalizedAtDualZero (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) :
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (lift (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
        (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))).left
      (D.poincarePullback f)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f).left) := by
  obtain ⟨e⟩ := D.normalizedAtDualZero
  let i := lift (1 : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f))
    (𝟙 (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
  let j := lift (1 : A ⟶ D.abelian) (𝟙 A)
  let c := UnbundledDualData.Construction.UnbundledPicard.DualData.baseChangeProjection A f
  let p := D.poincarePullbackOverMap f
  have h : i.left ≫ p.left = c.left ≫ j.left :=
    congrArg (fun z : (Over.map f).obj (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) ⟶
      D.abelian ⊗ A => z.left) (D.poincarePullbackOverMap_dualZero f)
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp c.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback c.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c.left⟩

/-- Base change of all the dual abelian data, including the representing
property and the normalized universal Poincare bundle. -/
def UnbundledDualData.Construction.UnbundledPicard.DualData.pullback (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : S' ⟶ S) : UnbundledDualData.Construction.UnbundledPicard.DualData (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) where
  abelian := UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian f
  group := Functor.grpObjObj
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd D.abelian.hom f))
  smooth := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.abelian.hom f))
  connected := inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd D.abelian.hom f))
  representable := D.pullbackRepresentable f
  origin := D.pullbackRepresentable_origin f
  poincare := D.poincarePullback f
  poincareHomogeneous := D.poincarePullback_homogeneous f
  universalClass := D.poincarePullback_universalClass f
  normalizedAtAbelianZero := D.poincarePullback_normalizedAtAbelianZero f
  normalizedAtDualZero := D.poincarePullback_normalizedAtDualZero f

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms
