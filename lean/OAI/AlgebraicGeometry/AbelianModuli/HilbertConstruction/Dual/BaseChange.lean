import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! The dual abelian scheme represents the homogeneous Picard sheaf after base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

/-- Restriction of the represented presheaf is represented by the base change. -/
def Data.DualAbelianData.restrictedRepresentable (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    ((Over.map f).op ⋙ A.homogeneousPicardSheaf.obj).RepresentableBy
      (D.abelian.pullback f).scheme where
  homEquiv {T} := (D.abelian.baseChangePointsEquiv f T).trans
    D.representable.homEquiv
  homEquiv_comp {T U} h a := by
    exact (congrArg D.representable.homEquiv
      (D.abelian.baseChangePointsEquiv_precomp f h a)).trans
        (D.representable.homEquiv_comp ((Over.map f).map h)
          (D.abelian.baseChangePointsEquiv f U a))

/-- The base change of the dual represents the homogeneous Picard sheaf
of the base-changed abelian scheme. -/
def Data.DualAbelianData.pullbackRepresentable (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (A.pullback f).homogeneousPicardSheaf.obj.RepresentableBy (D.abelian.pullback f).scheme :=
  (D.restrictedRepresentable f).ofIso
    (((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (A.homogeneousPicardSheafBaseChangeIso f)).symm)

/-- The representing equivalence after base change preserves the origin. -/
theorem Data.DualAbelianData.pullbackRepresentable_origin (D : Data.DualAbelianData A) (f : S' ⟶ S) (T : Over S') :
    (D.pullbackRepresentable f).homEquiv (1 : T ⟶ (D.abelian.pullback f).scheme) =
      (A.pullback f).trivialHomogeneousPicardClass T := by
  apply (A.homogeneousPicardBaseChangeEquiv f T).injective
  change A.homogeneousPicardBaseChangeEquiv f T
    ((A.homogeneousPicardBaseChangeEquiv f T).symm
      (D.representable.homEquiv (D.abelian.baseChangePointsEquiv f T 1))) = _
  rw [Equiv.apply_symm_apply, A.trivialHomogeneousPicardClass_baseChange]
  exact (congrArg D.representable.homEquiv
    (D.abelian.baseChangePointsMulEquiv f T).map_one).trans
      (D.origin ((Over.map f).obj T))

/-- The projection from a base change, viewed over the original base. -/
def Data.DualAbelianData.baseChangeProjection (B : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) :
    (Over.map f).obj (B.pullback f).scheme ⟶ B.scheme :=
  B.baseChangePointsEquiv f (B.pullback f).scheme (𝟙 _)

/-- The map from the product of the two changed abelian schemes to the old product. -/
def Data.DualAbelianData.poincarePullbackOverMap (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (Over.map f).obj ((D.abelian.pullback f).scheme ⊗ (A.pullback f).scheme) ⟶
      D.abelian.scheme ⊗ A.scheme :=
  (A.baseChangeFamilyIso f (D.abelian.pullback f).scheme).hom ≫
    (Data.DualAbelianData.baseChangeProjection D.abelian f ▷ A.scheme)

@[reassoc (attr := simp)]
theorem Data.DualAbelianData.poincarePullbackOverMap_fst (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    D.poincarePullbackOverMap f ≫ fst D.abelian.scheme A.scheme =
      (Over.map f).map (fst (D.abelian.pullback f).scheme (A.pullback f).scheme) ≫
        Data.DualAbelianData.baseChangeProjection D.abelian f := by
  rw [Data.DualAbelianData.poincarePullbackOverMap, Category.assoc, whiskerRight_fst,
    A.baseChangeFamilyIso_hom_fst_assoc]

@[reassoc (attr := simp)]
theorem Data.DualAbelianData.poincarePullbackOverMap_snd (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    D.poincarePullbackOverMap f ≫ snd D.abelian.scheme A.scheme =
      A.baseChangePointsEquiv f ((D.abelian.pullback f).scheme ⊗ (A.pullback f).scheme)
        (snd (D.abelian.pullback f).scheme (A.pullback f).scheme) := by
  rw [Data.DualAbelianData.poincarePullbackOverMap, Category.assoc, whiskerRight_snd,
    A.baseChangeFamilyIso_hom_snd]

@[simp]
theorem Data.DualAbelianData.baseChangeProjection_comp (B : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    {T : Over S'} (a : T ⟶ (B.pullback f).scheme) :
    (Over.map f).map a ≫ Data.DualAbelianData.baseChangeProjection B f = B.baseChangePointsEquiv f T a :=
  (B.baseChangePointsEquiv_precomp f a (𝟙 _)).symm.trans
    (congrArg (B.baseChangePointsEquiv f T) (Category.comp_id a))

@[simp]
theorem Data.DualAbelianData.baseChangePointsEquiv_one (B : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    B.baseChangePointsEquiv f T 1 = 1 :=
  (B.baseChangePointsMulEquiv f T).map_one

/-- The Poincare product map respects the zero section in the abelian factor. -/
theorem Data.DualAbelianData.poincarePullbackOverMap_abelianZero (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (Over.map f).map
        (lift (𝟙 (D.abelian.pullback f).scheme)
          (1 : (D.abelian.pullback f).scheme ⟶ (A.pullback f).scheme)) ≫
        D.poincarePullbackOverMap f =
      Data.DualAbelianData.baseChangeProjection D.abelian f ≫
        lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ A.scheme) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc, ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, Data.DualAbelianData.baseChangeProjection]
  · simp [Category.assoc, ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp]

/-- The Poincare product map respects the zero section in the dual factor. -/
theorem Data.DualAbelianData.poincarePullbackOverMap_dualZero (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (Over.map f).map
        (lift (1 : (A.pullback f).scheme ⟶ (D.abelian.pullback f).scheme)
          (𝟙 (A.pullback f).scheme)) ≫ D.poincarePullbackOverMap f =
      Data.DualAbelianData.baseChangeProjection A f ≫
        lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc, ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp]
  · simp [Category.assoc, ← Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_precomp, Data.DualAbelianData.baseChangeProjection]

/-- The actual Poincare line bundle after change of base. -/
def Data.DualAbelianData.poincarePullback (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    Line.Bundles.LineBundle ((D.abelian.pullback f).scheme ⊗ (A.pullback f).scheme).left :=
  Line.Bundles.LineBundle.pullback (D.poincarePullbackOverMap f).left D.poincare

/-- The pulled-back Poincare class is the restriction of the old universal class. -/
theorem Data.DualAbelianData.poincarePullback_comparison (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app
        (.op (D.abelian.pullback f).scheme) (Line.Bundles.LineBundle.classOf (D.poincarePullback f)) =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (Data.DualAbelianData.baseChangeProjection D.abelian f).op
        (Line.Bundles.LineBundle.classOf D.poincare) := by
  let e := Picard.BaseChange.familyBaseChangeIso A.scheme f (D.abelian.pullback f).scheme
  let c := Data.DualAbelianData.baseChangeProjection D.abelian f ▷ A.scheme
  exact (congrArg (Line.Bundles.LineBundle.pullbackClass e.inv)
    (Line.Bundles.LineBundle.pullbackClass_comp e.hom c.left (Line.Bundles.LineBundle.classOf D.poincare))).trans
      ((Line.Bundles.LineBundle.pullbackIso e).left_inv
        (Line.Bundles.LineBundle.pullbackClass c.left (Line.Bundles.LineBundle.classOf D.poincare)))

/-- The pulled-back Poincare bundle is homogeneous. -/
theorem Data.DualAbelianData.poincarePullback_homogeneous (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (A.pullback f).IsHomogeneousPicardClass (D.abelian.pullback f).scheme
      (Line.Bundles.LineBundle.classOf (D.poincarePullback f)) := by
  apply (A.isHomogeneousPicardClass_baseChange_iff f (D.abelian.pullback f).scheme _).mpr
  exact (congrArg (A.IsHomogeneousPicardClass ((Over.map f).obj (D.abelian.pullback f).scheme))
    (D.poincarePullback_comparison f)).mpr
      (D.poincareHomogeneous.pullback A (Data.DualAbelianData.baseChangeProjection D.abelian f))

/-- The homogeneous presheaf class of the original Poincare bundle. -/
def Data.DualAbelianData.poincareRawClass (D : Data.DualAbelianData A) :
    A.homogeneousPicardPresheaf.obj (.op D.abelian.scheme) :=
  ⟨Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩

/-- The homogeneous presheaf class of the pulled-back Poincare bundle. -/
def Data.DualAbelianData.poincarePullbackRawClass (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (A.pullback f).homogeneousPicardPresheaf.obj (.op (D.abelian.pullback f).scheme) :=
  ⟨Line.Bundles.LineBundle.classOf (D.poincarePullback f), D.poincarePullback_homogeneous f⟩

/-- Comparison of the Poincare classes in the homogeneous presheaves. -/
theorem Data.DualAbelianData.poincarePullbackRawClass_comparison (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (A.homogeneousPicardPresheafBaseChangeIso f).hom.app (.op (D.abelian.pullback f).scheme)
        (D.poincarePullbackRawClass f) =
      A.homogeneousPicardPresheaf.map (Data.DualAbelianData.baseChangeProjection D.abelian f).op D.poincareRawClass :=
  Subtype.ext (D.poincarePullback_comparison f)

/-- Compatibility of the representing bijection with the sheaf comparison. -/
theorem Data.DualAbelianData.pullbackRepresentable_comparison (D : Data.DualAbelianData A) (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (D.abelian.pullback f).scheme) :
    A.homogeneousPicardBaseChangeEquiv f T ((D.pullbackRepresentable f).homEquiv a) =
      D.representable.homEquiv (D.abelian.baseChangePointsEquiv f T a) :=
  (A.homogeneousPicardBaseChangeEquiv f T).apply_symm_apply _

/-- The Poincare class remains the universal element after base change. -/
theorem Data.DualAbelianData.poincarePullback_universalClass (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    (D.pullbackRepresentable f).homEquiv (𝟙 (D.abelian.pullback f).scheme) =
      (toSheafify (Scheme.fppfTopology.over S') (A.pullback f).homogeneousPicardPresheaf).app
        (.op (D.abelian.pullback f).scheme) (D.poincarePullbackRawClass f) := by
  let c := Data.DualAbelianData.baseChangeProjection D.abelian f
  let unitMap := toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf
  apply (A.homogeneousPicardBaseChangeEquiv f (D.abelian.pullback f).scheme).injective
  exact (D.pullbackRepresentable_comparison f _ (𝟙 _)).trans
    ((D.representable.homEquiv_eq c).trans
      ((congrArg (A.homogeneousPicardSheaf.obj.map c.op) D.universalClass).trans
        ((unitMap.naturality_apply c.op D.poincareRawClass).symm.trans
          ((congrArg (fun z => unitMap.app (.op ((Over.map f).obj (D.abelian.pullback f).scheme)) z)
            (D.poincarePullbackRawClass_comparison f).symm).trans
              (A.toHomogeneousPicard_baseChange_apply f _ (D.poincarePullbackRawClass f)).symm))))

/-- Normalization at the abelian zero section is preserved by base change. -/
theorem Data.DualAbelianData.poincarePullback_normalizedAtAbelianZero (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    Nonempty ((Line.Bundles.LineBundle.pullback
      (lift (𝟙 (D.abelian.pullback f).scheme)
        (1 : (D.abelian.pullback f).scheme ⟶ (A.pullback f).scheme)).left
      (D.poincarePullback f)).sheaf ≅ Line.Bundles.structureModule (D.abelian.pullback f).scheme.left) := by
  obtain ⟨e⟩ := D.normalizedAtAbelianZero
  let i := lift (𝟙 (D.abelian.pullback f).scheme)
    (1 : (D.abelian.pullback f).scheme ⟶ (A.pullback f).scheme)
  let j := lift (𝟙 D.abelian.scheme) (1 : D.abelian.scheme ⟶ A.scheme)
  let c := Data.DualAbelianData.baseChangeProjection D.abelian f
  let p := D.poincarePullbackOverMap f
  have h : i.left ≫ p.left = c.left ≫ j.left :=
    congrArg (fun z : (Over.map f).obj (D.abelian.pullback f).scheme ⟶
      D.abelian.scheme ⊗ A.scheme => z.left) (D.poincarePullbackOverMap_abelianZero f)
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp c.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback c.left).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso c.left⟩

/-- Normalization at the dual zero section is preserved by base change. -/
theorem Data.DualAbelianData.poincarePullback_normalizedAtDualZero (D : Data.DualAbelianData A) (f : S' ⟶ S) :
    Nonempty ((Line.Bundles.LineBundle.pullback
      (lift (1 : (A.pullback f).scheme ⟶ (D.abelian.pullback f).scheme)
        (𝟙 (A.pullback f).scheme)).left
      (D.poincarePullback f)).sheaf ≅ Line.Bundles.structureModule (A.pullback f).scheme.left) := by
  obtain ⟨e⟩ := D.normalizedAtDualZero
  let i := lift (1 : (A.pullback f).scheme ⟶ (D.abelian.pullback f).scheme)
    (𝟙 (A.pullback f).scheme)
  let j := lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)
  let c := Data.DualAbelianData.baseChangeProjection A f
  let p := D.poincarePullbackOverMap f
  have h : i.left ≫ p.left = c.left ≫ j.left :=
    congrArg (fun z : (Over.map f).obj (A.pullback f).scheme ⟶
      D.abelian.scheme ⊗ A.scheme => z.left) (D.poincarePullbackOverMap_dualZero f)
  exact ⟨(Scheme.Modules.pullbackComp i.left p.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp c.left j.left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback c.left).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso c.left⟩

/-- Base change of all the dual abelian data, including the representing
property and the normalized universal Poincare bundle. -/
def Data.DualAbelianData.pullback (D : Data.DualAbelianData A) (f : S' ⟶ S) : Data.DualAbelianData (A.pullback f) where
  abelian := D.abelian.pullback f
  representable := D.pullbackRepresentable f
  origin := D.pullbackRepresentable_origin f
  poincare := D.poincarePullback f
  poincareHomogeneous := D.poincarePullback_homogeneous f
  universalClass := D.poincarePullback_universalClass f
  normalizedAtAbelianZero := D.poincarePullback_normalizedAtAbelianZero f
  normalizedAtDualZero := D.poincarePullback_normalizedAtDualZero f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
