import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.HomogeneousPicardEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupLaw

/-! # Poincare Class Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareClassAdditivity.RelativePoincareClasses

noncomputable section

section

/-! Actual normalized Poincare classes are additive in the specified
dual group law over locally noetherian bases, on arbitrary quasi-compact
quasi-separated parameter schemes. Rigidity and effective descent prove it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.HomogeneousPicardEvaluation.RelativeNormalizedPicard

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over S}

theorem representable_mul (a b : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv (a * b) =
      D.representable.homEquiv a * D.representable.homEquiv b := by
  have h : letI := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
      D.representable.homEquiv (a * b) =
        D.representable.homEquiv a * D.representable.homEquiv b := by
    let := Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroup D
    exact (Picard.Homomorphisms.CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).map_mul a b
  rw [DualGroupLaw.dualPicardGroup_eq_given_relative D] at h
  exact h

theorem poincareClass_mul (a b : T ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D (a * b) = Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D a * Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D b := by
  have h := (congrArg (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom A T) (representable_mul D a b)).trans
    ((Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom A T).map_mul _ _)
  simpa only [Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardSheafInclusionHom_apply, ← Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation] using h

def familyClass (t : T ⟶ D.abelian.scheme) : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (t ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsLocallyNoetherian S] in
theorem familyClass_zero (t : T ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (familyClass D t) = 1 := by
  rw [familyClass, PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.zero_class_naturality]
  have h : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) = 1 := Quotient.sound D.normalizedAtAbelianZero
  rw [h, map_one]

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem familyClass_mul (a b : T ⟶ D.abelian.scheme) :
    familyClass D (a * b) = familyClass D a * familyClass D b := by
  have hs : (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D (a * b)) =
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D a * familyClass D b) := by
    exact (poincareClass_mul D a b).trans
      (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul A.scheme T (familyClass D a) (familyClass D b)).symm
  have h := HomogeneousPicardEvaluation.RelativeNormalizedPicard.normalizedClass_eq_of_picard_eq A _ _ hs
  have hab : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (familyClass D a * familyClass D b) = 1 := by
    rw [map_mul, familyClass_zero, familyClass_zero, one_mul]
  rw [PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ (familyClass_zero D (a * b)),
    PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self A T _ hab] at h
  exact h

theorem familyClass_one : familyClass D (1 : T ⟶ D.abelian.scheme) = 1 := by
  have h := familyClass_mul D (1 : T ⟶ D.abelian.scheme) 1
  rw [one_mul] at h
  exact (mul_left_cancel ((mul_one _).trans h)).symm

def familyClassHom : (T ⟶ D.abelian.scheme) →* HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left where
  toFun := familyClass D
  map_one' := familyClass_one D
  map_mul' := familyClass_mul D

end

/-! The actual Poincare bundle on a varying family defines a bilinear
pairing of points with values in line-bundle classes on arbitrary quasi-compact
quasi-separated parameter schemes over a locally noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.HomogeneousPicardEvaluation.RelativeNormalizedPicard

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over S}

def pairClass (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) : HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift t a).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsLocallyNoetherian S] in
theorem pairClass_eq_evaluate (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D t a = HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass A (familyClass D t) a := by
  have h : HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection A a ≫ (t ▷ A.scheme) = lift t a := by
    apply hom_ext <;> simp [HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection]
  exact (congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (congrArg Over.Hom.left h).symm).trans
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection A a).left (t ▷ A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem pairClass_mul_left (s t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D (s * t) a = pairClass D s a * pairClass D t a := by
  simp only [pairClass_eq_evaluate, HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass, familyClass_mul, map_mul]

theorem pairClass_one_left (a : T ⟶ A.scheme) : pairClass D 1 a = 1 := by
  rw [pairClass_eq_evaluate, HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass, familyClass_one, map_one]

theorem pairClass_mul_right (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) :
    pairClass D t (a * b) = pairClass D t a * pairClass D t b := by
  simp only [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass_mul A (familyClass D t)
    (D.poincareHomogeneous.pullback A t) (familyClass_zero D t) a b

omit [IsLocallyNoetherian S] [CompactSpace T.left] [QuasiSeparatedSpace T.left] in
theorem pairClass_one_right (t : T ⟶ D.abelian.scheme) : pairClass D t 1 = 1 := by
  rw [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass_one A (familyClass D t) (familyClass_zero D t)

def pairLeftHom (a : T ⟶ A.scheme) : (T ⟶ D.abelian.scheme) →* HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
  toFun := fun t => pairClass D t a
  map_one' := pairClass_one_left D a
  map_mul' := fun s t => pairClass_mul_left D s t a

def pairRightHom (t : T ⟶ D.abelian.scheme) : (T ⟶ A.scheme) →* HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left where
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

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareClassAdditivity.RelativePoincareClasses
