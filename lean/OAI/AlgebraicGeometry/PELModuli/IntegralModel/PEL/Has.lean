import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Has -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-!
Integral PEL objects and actual comparisons of their generic fibers.
These reuse ReferenceFamily's Hermitian datum, ring action, Rosati condition, and
dual-number Lie eigenspaces, and HilbertConstruction's polarized abelian schemes.

A comparison is an isomorphism of the underlying abelian and dual schemes
preserving the actual polarization, Poincare class, full level, and action.
It is not a cohomology-comparison or model-existence assertion. The existence
of an integral model with this comparison remains in the theorem conclusion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

def Base.ArithmeticBaseExtension.integralEmbedding
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (iota : E →+* K) :
    NumberField.RingOfIntegers E →+* B.R :=
  (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R).comp
    (NumberField.RingOfIntegers.mapRingHom
      ((algebraMap K B.extension.carrier).comp iota))

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Base.ArithmeticBaseExtension.integralEmbedding_toField
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (iota : E →+* K)
    (a : NumberField.RingOfIntegers E) :
    B.toField (B.integralEmbedding iota a) =
      algebraMap K B.extension.carrier (iota (a : E)) := by
  change ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField B.extension.carrier
    B.denominator B.denominator_ne_zero
    (algebraMap (NumberField.RingOfIntegers B.extension.carrier) B.R _) = _
  rw [ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap]
  rfl

/-- Polarized abelian data with an actual integral action, over any base. -/
structure PEL.Has.PolarizedActionData (E : Type) [Field E] (g : ℕ)
    (δ : Fin g → ℕ) (N : ℕ) (S : Scheme) where
  polarized : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S
  action : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) polarized.abelian

variable {g N : ℕ} {δ : Fin g → ℕ} {S T Z : Scheme}

/-- An isomorphism of two pulled-back PEL families on a common base.
All compatibility clauses are equalities of the specified geometric data. -/
structure PEL.Has.PulledBackPELDataIso
    (A : PEL.Has.PolarizedActionData E g δ N S) (B : PEL.Has.PolarizedActionData E g δ N T)
    (f : Z ⟶ S) (h : Z ⟶ T) where
  abelian : (A.polarized.abelian.pullback f).scheme ≅
    (B.polarized.abelian.pullback h).scheme
  dual : (A.polarized.dual.abelian.pullback f).scheme ≅
    (B.polarized.dual.abelian.pullback h).scheme
  abelianGroup : IsMonHom abelian.hom
  dualGroup : IsMonHom dual.hom
  polarization : (Over.pullback f).map A.polarized.polarization.isogeny.hom ≫ dual.hom =
    abelian.hom ≫ (Over.pullback h).map B.polarized.polarization.isogeny.hom
  poincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((dual.hom ⊗ₘ abelian.hom).left ≫ AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap B.polarized.dual h)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.polarized.dual.poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare)
  level : ∀ (V : Over Z)
    (c : LocallyConstant V.left (Multiplicative (Fin (2 * g) → ZMod N))),
    ((A.polarized.level.pullback f).hom.app (.op V) c).val ≫ abelian.hom =
      ((B.polarized.level.pullback h).hom.app (.op V) c).val
  action : ∀ a : NumberField.RingOfIntegers E,
    (A.action.pullback f).map a ≫ abelian.hom =
      abelian.hom ≫ (B.action.pullback h).map a

attribute [instance] PEL.Has.PulledBackPELDataIso.abelianGroup PEL.Has.PulledBackPELDataIso.dualGroup

def PEL.Has.PulledBackPELDataIso.refl
    (A : PEL.Has.PolarizedActionData E g δ N S) (f : Z ⟶ S) :
    PEL.Has.PulledBackPELDataIso A A f f where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 (A.polarized.abelian.pullback f).scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 (A.polarized.dual.abelian.pullback f).scheme))
  polarization := (Category.comp_id _).trans (Category.id_comp _).symm
  poincare := by simp
  level V c := by simp
  action a := by simp

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

/-- The integral Lie condition uses the base's O_E-algebra map, so that it
also makes sense in positive characteristic. -/
def PEL.Has.HasIntegralLieRanks (R : Type) [CommRing R]
    (iotaO : NumberField.RingOfIntegers E →+* R)
    (T : Over (Spec (.of R))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (j : R →+* F)
    (p : Spec (.of F) ⟶ T.left),
    p ≫ T.hom = Spec.map (CommRingCat.ofHom j) →
    ∀ τ : E ≃ₐ[ℚ] E,
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback p) (ρ.pullback p)
        (j.comp (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)))
        (P.lieRank τ)

/-- An actual integral PEL object. These are objects of the moduli problem;
representability, smoothness of the moduli space, and spreading are not fields. -/
structure PEL.Has.IntegralPELObject (R : Type) [CommRing R]
    (iotaO : NumberField.RingOfIntegers E →+* R) (N : ℕ)
    (T : Over (Spec (.of R))) where
  data : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N T.left
  rosati : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation data.polarized data.action
  lieRanks : PEL.Has.HasIntegralLieRanks P R iotaO T data.polarized.abelian data.action

def PEL.Has.characteristicZeroPELData
    {K : Type} [Field K] [NumberField K] {iota : E →+* K}
    {M : Over (Spec (.of K))} (U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M) :
    PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N M.left where
  polarized := U.polarized
  action := U.action

/-- Adapter to ReferenceFamily's concrete fine-moduli predicate. -/
def PEL.Has.IsFinePELModuli
    {K : Type} [Field K] [NumberField K] (iota : E →+* K)
    (N : ℕ) (M : Over (Spec (.of K))) (U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M) : Prop :=
  (AbelianModuli.ReferenceFamily.Models.FinePELModel.mk M U).IsFine

/-- Explicit fine full-level and stabilizer condition. No coprimality with
the polarization degree is imposed: auxiliary level is handled by ReferenceFamily. -/
def PEL.Has.IsSufficientlyDeepFullLevel (N : ℕ) : Prop :=
  3 ≤ N ∧
    ∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
      ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1

/-- A model of the reduced characteristic-zero moduli and its universal
PEL family. The generic identification is a scheme isomorphism, and the
family identification is the explicit geometric isomorphism defined above. -/
structure PEL.Has.IntegralPELSpread
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (N : ℕ) (M : Over (Spec (.of K))) (U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M)
    (B : Base.ArithmeticBaseExtension K κ) where
  toOver : Over B.base
  universal : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N toOver
  genericIso : (Over.pullback B.generic).obj toOver ≅
    (Over.pullback B.fieldExtension).obj (Reduction.reduction M)
  familyIso : PEL.Has.PulledBackPELDataIso universal.data (PEL.Has.characteristicZeroPELData P U)
    (pullback.fst toOver.hom B.generic)
    (genericIso.hom.left ≫ pullback.fst (Reduction.reduction M).hom B.fieldExtension ≫
      (Reduction.reductionι M).left)

/-- The restricted fine-moduli property is stated on all actual reduced
test schemes, with pullback classification expressed by the geometric iso. -/
def PEL.Has.IntegralPELSpread.IsReducedPELModuli
    {K : Type} [Field K] [NumberField K] {iota : E →+* K} {κ : K →+* ℂ}
    {N : ℕ} {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
    {B : Base.ArithmeticBaseExtension K κ} (V : PEL.Has.IntegralPELSpread P iota κ N M U B) : Prop :=
  ∀ (Y : Over B.base) [IsReduced Y.left]
    (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Y),
    ∃! f : Y ⟶ V.toOver,
      Nonempty (PEL.Has.PulledBackPELDataIso V.universal.data A.data f.left (𝟙 Y.left))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
