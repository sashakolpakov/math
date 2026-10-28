import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison

/-! # Poincare Class -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass.PoincareClasses

noncomputable section

section

/-! The actual normalized Poincare family is additive in the given dual
group law. Rigidity identifies that law with Picard tensor product, and
normalized descent upgrades sheaf equality to an equality of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))}

theorem representable_mul (a b : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv (a * b) =
      D.representable.homEquiv a * D.representable.homEquiv b := by
  have h : letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
      D.representable.homEquiv (a * b) =
        D.representable.homEquiv a * D.representable.homEquiv b := by
    let := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
    exact (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).map_mul a b
  rw [Picard.Homomorphisms.DualGroupComparison.Construction.dualPicardGroup_eq_given D] at h
  exact h

theorem poincareClass_mul (a b : T ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D (a * b) = Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D a * Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D b := by
  have h := (congrArg (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom A T) (representable_mul D a b)).trans
    ((Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom A T).map_mul _ _)
  simpa only [Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom_apply, ← Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation] using h

def familyClass (t : T ⟶ D.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (t ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsAlgClosed k] in
theorem familyClass_zero (t : T ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (familyClass D t) = 1 := by
  rw [familyClass, Picard.Inv.NormalizedPicard.zero_class_naturality]
  have h : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) = 1 := Quotient.sound D.normalizedAtAbelianZero
  rw [h, map_one]

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem familyClass_mul (a b : T ⟶ D.abelian.scheme) :
    familyClass D (a * b) = familyClass D a * familyClass D b := by
  have hs : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D (a * b)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D a * familyClass D b) := by
    exact (poincareClass_mul D a b).trans
      (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul A.scheme T (familyClass D a) (familyClass D b)).symm
  have h := Picard.Inv.NormalizedPicard.normalizedClass_eq_of_picard_eq A _ _ hs
  have hab : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (familyClass D a * familyClass D b) = 1 := by
    rw [map_mul, familyClass_zero, familyClass_zero, one_mul]
  rw [Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ (familyClass_zero D (a * b)),
    Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ hab] at h
  exact h

theorem familyClass_one : familyClass D (1 : T ⟶ D.abelian.scheme) = 1 := by
  have h := familyClass_mul D (1 : T ⟶ D.abelian.scheme) 1
  rw [one_mul] at h
  exact (mul_left_cancel ((mul_one _).trans h)).symm

def familyClassHom : (T ⟶ D.abelian.scheme) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left where
  toFun := familyClass D
  map_one' := familyClass_one D
  map_mul' := familyClass_mul D

end

section

/-! The Poincare bundle gives a bilinear pairing on scheme-valued points
with values in actual line-bundle classes. No reducedness of the test
scheme is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardEvaluation.NormalizedPicard

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))}

def pairClass (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift t a).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsAlgClosed k] in
theorem pairClass_eq_evaluate (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D t a = HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass A (familyClass D t) a := by
  have h : HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection A a ≫ (t ▷ A.scheme) = lift t a := by
    apply hom_ext <;> simp [HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection]
  exact (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (congrArg Over.Hom.left h).symm).trans
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (HomogeneousPicardEvaluation.NormalizedPicard.evaluationSection A a).left (t ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem pairClass_mul_left (s t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D (s * t) a = pairClass D s a * pairClass D t a := by
  simp only [pairClass_eq_evaluate, HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass, familyClass_mul, map_mul]

theorem pairClass_one_left (a : T ⟶ A.scheme) : pairClass D 1 a = 1 := by
  rw [pairClass_eq_evaluate, HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass, familyClass_one, map_one]

theorem pairClass_mul_right (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) :
    pairClass D t (a * b) = pairClass D t a * pairClass D t b := by
  simp only [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass_mul A (familyClass D t)
    (D.poincareHomogeneous.pullback A t) (familyClass_zero D t) a b

omit [IsAlgClosed k] [CompactSpace T.left] [QuasiSeparatedSpace T.left] in
theorem pairClass_one_right (t : T ⟶ D.abelian.scheme) : pairClass D t 1 = 1 := by
  rw [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.NormalizedPicard.evaluateClass_one A (familyClass D t) (familyClass_zero D t)

def pairLeftHom (a : T ⟶ A.scheme) : (T ⟶ D.abelian.scheme) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := fun t => pairClass D t a
  map_one' := pairClass_one_left D a
  map_mul' := fun s t => pairClass_mul_left D s t a

def pairRightHom (t : T ⟶ D.abelian.scheme) : (T ⟶ A.scheme) →* AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := pairClass D t
  map_one' := pairClass_one_right D t
  map_mul' := pairClass_mul_right D t

theorem pairClass_pow_left (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (n : ℕ) :
    pairClass D (t ^ n) a = pairClass D t a ^ n := (pairLeftHom D a).map_pow t n

theorem pairClass_pow_right (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (n : ℕ) :
    pairClass D t (a ^ n) = pairClass D t a ^ n := (pairRightHom D t).map_pow a n

theorem pairClass_inv_right (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D t a⁻¹ = (pairClass D t a)⁻¹ := (pairRightHom D t).map_inv a

end

/-! The Rosati similitude equation yields a fixed power identity for the
actual line bundle obtained by restricting Poincare to the polarization
diagonal. This is the geometric input for bounding isogeny graphs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison.Construction

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

omit [IsAlgClosed k] in
theorem pairClass_precomp {T U : Over (Spec (.of k))} (p : U ⟶ T)
    (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback p.left (pairClass D t a) = pairClass D (p ≫ t) (p ≫ a) := by
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp p.left (lift t a).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
    (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
      (congrArg Over.Hom.left (comp_lift p t a)))

omit [IsAlgClosed k] in
theorem pairClass_adjoint (f : A.scheme ⟶ A.scheme)
    (q : D.abelian.scheme ⟶ D.abelian.scheme)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    {T : Over (Spec (.of k))} (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D (t ≫ q) a = pairClass D t (a ≫ f) := by
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift t a).left) hq
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp] at h
  have hl : (lift t a).left ≫ (q ⊗ₘ 𝟙 A.scheme).left = (lift (t ≫ q) a).left := by
    simpa only [Category.comp_id, Over.comp_left] using congrArg Over.Hom.left (lift_map t a q (𝟙 A.scheme))
  have hr : (lift t a).left ≫ (𝟙 D.abelian.scheme ⊗ₘ f).left = (lift t (a ≫ f)).left := by
    simpa only [Category.comp_id, Over.comp_left] using congrArg Over.Hom.left (lift_map t a (𝟙 D.abelian.scheme) f)
  rw [hl, hr] at h
  exact h

def polarizationLine (ell : A.scheme ⟶ D.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (lift ell (𝟙 A.scheme)).left D.poincare

local instance abelian_compact : CompactSpace A.scheme.left :=
  QuasiCompact.compactSpace_of_compactSpace A.scheme.hom

local instance abelian_quasiSeparated : QuasiSeparatedSpace A.scheme.left :=
  quasiSeparatedSpace_of_quasiSeparated A.scheme.hom

/-- The exponent depends only on the similitude multiplier, and the
identity concerns the fixed actual polarization line bundle. -/
theorem polarizationLine_pullback_class
    (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell]
    (f : A.scheme ⟶ A.scheme) (q : D.abelian.scheme ⟶ D.abelian.scheme)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (n : ℕ) (h : f ≫ ell ≫ q = ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ ell) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationLine D ell)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationLine D ell) ^ n := by
  have hn : f ≫ ell ≫ q = ell ^ n := by
    rw [h, MonObj.pow_comp, Category.id_comp]
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (pairClass D ell (𝟙 A.scheme)) =
    pairClass D ell (𝟙 A.scheme) ^ n
  rw [pairClass_precomp, Category.comp_id]
  have ha := pairClass_adjoint D f q hq (f ≫ ell) (𝟙 A.scheme)
  rw [Category.id_comp, Category.assoc, hn] at ha
  exact ha.symm.trans (pairClass_pow_left D ell (𝟙 A.scheme) n)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass.PoincareClasses
