import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.HomogeneousPicardEvaluation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualGroupLaw
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PicardFunctions
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Poincare Eq -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq.RelativePoincareClasses
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.HomogeneousPicardEvaluation.RelativeNormalizedPicard
section

/-! Actual normalized Poincare classes are additive in the specified
dual group law over reduced locally noetherian bases, on reduced
noetherian parameter schemes. Rigidity and effective descent prove it. -/

open Opposite

variable {S : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
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

def familyClass (t : T ⟶ D.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (t ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem familyClass_zero (t : T ⟶ D.abelian.scheme) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (familyClass D t) = 1 := by
  rw [familyClass, Picard.Inv.NormalizedPicard.zero_class_naturality]
  have h : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) = 1 := Quotient.sound D.normalizedAtAbelianZero
  rw [h, map_one]

variable [IsReduced T.left] [IsNoetherian T.left]

theorem familyClass_mul (a b : T ⟶ D.abelian.scheme) :
    familyClass D (a * b) = familyClass D a * familyClass D b := by
  have hs : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D (a * b)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (familyClass D a * familyClass D b) := by
    exact (poincareClass_mul D a b).trans
      (Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_mul A.scheme T (familyClass D a) (familyClass D b)).symm
  have h := HomogeneousPicardEvaluation.RelativeNormalizedPicard.normalizedClass_eq_of_picard_eq A _ _ hs
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

/-! The actual Poincare bundle on a varying family defines a bilinear
pairing of points with values in line-bundle classes on every reduced
noetherian parameter scheme. -/

variable {S : Scheme.{0}} [IsReduced S] [IsLocallyNoetherian S] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over S}

def pairClass (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift t a).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem pairClass_eq_evaluate (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D t a = HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass A (familyClass D t) a := by
  have h : HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection A a ≫ (t ▷ A.scheme) = lift t a := by
    apply hom_ext <;> simp [HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection]
  exact (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (congrArg Over.Hom.left h).symm).trans
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluationSection A a).left (t ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))

variable [IsReduced T.left] [IsNoetherian T.left]

theorem pairClass_mul_left (s t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D (s * t) a = pairClass D s a * pairClass D t a := by
  simp only [pairClass_eq_evaluate, HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass, familyClass_mul, map_mul]

theorem pairClass_one_left (a : T ⟶ A.scheme) : pairClass D 1 a = 1 := by
  rw [pairClass_eq_evaluate, HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass, familyClass_one, map_one]

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem pairClass_mul_right (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) :
    pairClass D t (a * b) = pairClass D t a * pairClass D t b := by
  simp only [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass_mul A (familyClass D t)
    (D.poincareHomogeneous.pullback A t) (familyClass_zero D t) a b

omit [IsReduced S] [IsLocallyNoetherian S] [AlgebraicGeometry.IsReduced T.left]
  [AlgebraicGeometry.IsNoetherian T.left] in
theorem pairClass_one_right (t : T ⟶ D.abelian.scheme) : pairClass D t 1 = 1 := by
  rw [pairClass_eq_evaluate]
  exact HomogeneousPicardEvaluation.RelativeNormalizedPicard.evaluateClass_one A (familyClass D t) (familyClass_zero D t)

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

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem pairClass_pow_right (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (n : ℕ) :
    pairClass D t (a ^ n) = pairClass D t a ^ n := (pairRightHom D t).map_pow a n

omit [IsReduced S] [IsLocallyNoetherian S] in
theorem pairClass_inv_right (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    pairClass D t a⁻¹ = (pairClass D t a)⁻¹ := (pairRightHom D t).map_inv a

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq.RelativePoincareClasses

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq

/-! Actual Poincare classes are additive in either operator on a varying
reduced noetherian family; the class on the dual factor detects the map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace RelativePoincareClasses
open OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction

variable {S : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def leftOperatorClass (d : D.abelian.scheme ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (D.abelian.scheme ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

def rightOperatorClass (u : A.scheme ⟶ A.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (D.abelian.scheme ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ u).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

theorem leftOperatorClass_eq_pair (d : D.abelian.scheme ⟶ D.abelian.scheme) :
    leftOperatorClass D d = pairClass D (fst D.abelian.scheme A.scheme ≫ d)
      (snd D.abelian.scheme A.scheme) := by
  apply congrArg (fun v => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass v (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  apply congrArg Over.Hom.left
  ext <;> simp only [tensorHom_fst, tensorHom_snd, lift_fst, lift_snd, Category.comp_id]

theorem rightOperatorClass_eq_pair (u : A.scheme ⟶ A.scheme) :
    rightOperatorClass D u = pairClass D (fst D.abelian.scheme A.scheme)
      (snd D.abelian.scheme A.scheme ≫ u) := by
  apply congrArg (fun v => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass v (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  apply congrArg Over.Hom.left
  ext <;> simp only [tensorHom_fst, tensorHom_snd, lift_fst, lift_snd, Category.comp_id]

theorem leftOperatorClass_injective : Function.Injective (leftOperatorClass D) := by
  intro d e h
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective D D.abelian.scheme
  have he := congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme)) h
  simpa only [leftOperatorClass, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass, tensorHom_id] using he

variable [IsReduced S] [IsNoetherian S]

local instance dualReduced : IsReduced D.abelian.scheme.left := by
  have : GeometricallyReduced D.abelian.scheme.hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth D.abelian.scheme.hom
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian D.abelian.scheme.hom

local instance dualNoetherian : IsNoetherian D.abelian.scheme.left := by
  let : IsLocallyNoetherian D.abelian.scheme.left := LocallyOfFiniteType.isLocallyNoetherian D.abelian.scheme.hom
  let : CompactSpace D.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace D.abelian.scheme.hom
  exact ⟨⟩

local instance productReduced : IsReduced (D.abelian.scheme ⊗ A.scheme).left :=
  PicardFunctions.RelativePicardFunctions.product_isReduced A D.abelian.scheme

local instance productNoetherian : IsNoetherian (D.abelian.scheme ⊗ A.scheme).left :=
  PicardFunctions.RelativePicardFunctions.product_isNoetherian A D.abelian.scheme

theorem leftOperatorClass_mul (d e : D.abelian.scheme ⟶ D.abelian.scheme) :
    leftOperatorClass D (d * e) = leftOperatorClass D d * leftOperatorClass D e := by
  rw [leftOperatorClass_eq_pair, leftOperatorClass_eq_pair, leftOperatorClass_eq_pair, MonObj.comp_mul]
  exact pairClass_mul_left D _ _ _

theorem rightOperatorClass_mul (u v : A.scheme ⟶ A.scheme) :
    rightOperatorClass D (u * v) = rightOperatorClass D u * rightOperatorClass D v := by
  rw [rightOperatorClass_eq_pair, rightOperatorClass_eq_pair, rightOperatorClass_eq_pair, MonObj.comp_mul]
  exact pairClass_mul_right D _ _ _

end RelativePoincareClasses

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq

end

end OAI
