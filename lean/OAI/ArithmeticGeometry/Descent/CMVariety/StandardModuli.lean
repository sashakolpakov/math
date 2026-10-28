import OAI.ArithmeticGeometry.Descent.CMVariety.ModuliObjects
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFiber
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Standard Moduli -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian

noncomputable section

/-!
A concrete arithmetic moduli interface for CMAbelianVariety.

The moduli problem is the presheaf of actual polarized full-level abelian
schemes with a finite tuple of algebraic endomorphisms. An arithmetic
subfunctor specifies relations or a PEL locus. A moduli space represents
that presheaf; its universal family is then constructed by Yoneda, rather
than included as an unrelated family. This definition does not establish
existence of a representing scheme.

Complex fiber presentations record the project's chosen projective
presentation of the actual abelian fiber. They provide no arithmetic
model or CM algebraicity assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- An arithmetic scheme representing the specified concrete enhanced
abelian moduli problem. The representation is part of what it means to
be that moduli space, not an assumption about the fields of its CM points. -/
structure ArithmeticAbelianModuli where
  dimension : ℕ
  polarizationType : Fin dimension → ℕ
  polarizationType_pos : ∀ i, 0 < polarizationType i
  polarizationType_chain : ∀ i j, i ≤ j → polarizationType i ∣ polarizationType j
  level : ℕ
  deepLevel : 3 ≤ level
  endomorphismCount : ℕ
  baseField : Subfield ℂ
  numberField : NumberField baseField
  parameter : Over (Spec (CommRingCat.of baseField))
  locallyFiniteType : LocallyOfFiniteType parameter.hom
  locus : Subfunctor (ModuliObjects.Abelian.enhancedAbelianModuliOver dimension polarizationType level
    endomorphismCount (Spec (CommRingCat.of baseField)))
  represents : locus.toFunctor.RepresentableBy parameter

attribute [instance] ArithmeticAbelianModuli.numberField
  ArithmeticAbelianModuli.locallyFiniteType

namespace ArithmeticAbelianModuli

abbrev space (M : ArithmeticAbelianModuli) : Scheme := M.parameter.left

/-- The universal moduli class is the class corresponding to the identity
of the representing scheme. -/
def universalClass (M : ArithmeticAbelianModuli) :
    ModuliObjects.Abelian.EnhancedAbelianClasses M.dimension M.polarizationType M.level
      M.endomorphismCount M.space :=
  (M.represents.homEquiv (𝟙 M.parameter)).val

/-- Choose an actual family representing the universal class. -/
def universal (M : ArithmeticAbelianModuli) :
    ModuliObjects.Abelian.EnhancedAbelianData M.dimension M.polarizationType M.level
      M.endomorphismCount M.space :=
  Quotient.out M.universalClass

theorem universal_classOf (M : ArithmeticAbelianModuli) :
    M.universal.classOf = M.universalClass := Quotient.out_eq _

/-- The constructed universal family classifies a morphism by its actual
pullback, as required by the moduli problem. -/
theorem universal_pullback_class (M : ArithmeticAbelianModuli)
    {T : Over (Spec (CommRingCat.of M.baseField))} (p : T ⟶ M.parameter) :
    (M.universal.pullback p.left).classOf = (M.represents.homEquiv p).val := by
  change ModuliObjects.Abelian.EnhancedAbelianClasses.pullback p.left M.universal.classOf = _
  rw [M.universal_classOf]
  exact (congrArg Subtype.val (M.represents.homEquiv_eq p)).symm

/-- The universal family recovers the unique classifying map of every
object in the arithmetic moduli locus. -/
theorem existsUnique_classifying_map (M : ArithmeticAbelianModuli)
    (T : Over (Spec (CommRingCat.of M.baseField)))
    (A : ModuliObjects.Abelian.EnhancedAbelianData M.dimension M.polarizationType M.level
      M.endomorphismCount T.left)
    (hA : A.classOf ∈ M.locus.obj (.op T)) :
    ∃! p : T ⟶ M.parameter, Nonempty (ModuliObjects.Abelian.EnhancedAbelianIso (M.universal.pullback p.left) A) := by
  let a : M.locus.toFunctor.obj (.op T) := ⟨A.classOf, hA⟩
  let p := M.represents.homEquiv.symm a
  have hp : M.represents.homEquiv p = a := M.represents.homEquiv.apply_symm_apply a
  refine ⟨p, ?_, ?_⟩
  · apply (ModuliObjects.Abelian.EnhancedAbelianData.classOf_eq_iff _ _).mp
    rw [M.universal_pullback_class, hp]
  · intro q hq
    apply M.represents.homEquiv.injective
    apply Subtype.ext
    rw [← M.universal_pullback_class, hp]
    exact (ModuliObjects.Abelian.EnhancedAbelianData.classOf_eq_iff _ _).mpr hq

/-- The underlying rational structure map of the arithmetic moduli scheme. -/
def rationalStructureMap (M : ArithmeticAbelianModuli) :
    M.space ⟶ Spec (CommRingCat.of ℚ) :=
  M.parameter.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ M.baseField))

instance rationalStructureMap_locallyFiniteType (M : ArithmeticAbelianModuli) :
    LocallyOfFiniteType M.rationalStructureMap := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℚ M.baseField))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  dsimp only [ArithmeticAbelianModuli.rationalStructureMap]
  infer_instance

end ArithmeticAbelianModuli

/-- A geometric projective presentation of an actual complex abelian
fiber, together with its group-preserving identification. -/
structure ComplexAbelianPresentation {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) where
  variety : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  comparison : A.scheme ≅ variety.toOver
  comparison_group : IsMonHom comparison.hom

attribute [instance] ComplexAbelianPresentation.comparison_group

/-- The standard arithmetic moduli interface, with geometric presentations
needed to use the repository's `CM.AbelianVariety` type. -/
structure StandardAbelianModuli extends ArithmeticAbelianModuli where
  complexFiber : ∀ p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ toArithmeticAbelianModuli.space,
    ComplexAbelianPresentation (toArithmeticAbelianModuli.universal.polarized.abelian.pullback p)

namespace StandardAbelianModuli

abbrev space (M : StandardAbelianModuli) : Scheme := M.toArithmeticAbelianModuli.space

def abelianAt (M : StandardAbelianModuli) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  (M.complexFiber p).variety

/-- The exact field-of-definition conclusion for a moduli point in CMAbelianVariety. -/
def IsAlgebraicPoint (M : StandardAbelianModuli) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space) : Prop :=
  ∃ (K : Subfield ℂ), NumberField K ∧
    ∃ pK : Spec (CommRingCat.of K) ⟶ M.space,
      Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p

/-- Arithmetic descent of the classified point produces a genuine model
of its abelian variety, with exactly the conclusion required by CMAbelianVariety. -/
theorem abelianAt_descends_of_point_descends
    (M : StandardAbelianModuli) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space)
    (hp : ∃ (K : Subfield ℂ), NumberField K ∧
      ∃ pK : Spec (CommRingCat.of K) ⟶ M.space,
        Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p) :
    AbelianFiber.HasNumberFieldModel (M.abelianAt p) := by
  let c := M.complexFiber p
  have : IsMonHom c.comparison.hom := c.comparison_group
  exact AbelianFiber.abelian_fiber_descends_of_parameter_descends
    M.toArithmeticAbelianModuli.universal.polarized.abelian p c.variety c.comparison hp

/-- Isolated points of this concrete arithmetic moduli space have
number-field models, including the underlying abelian group. -/
theorem abelianAt_descends_of_isolated
    (M : StandardAbelianModuli) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space)
    (hp : IsOpen {p (IsLocalRing.closedPoint ℂ)}) :
    AbelianFiber.HasNumberFieldModel (M.abelianAt p) :=
  M.abelianAt_descends_of_point_descends p
    (AlgebraicPoints.Abelian.complex_point_descends_of_isolated M.toArithmeticAbelianModuli.rationalStructureMap p hp)

end StandardAbelianModuli

end

end OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian
