import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Product

/-! # Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

noncomputable section

/-!
Candidate input for TateComparison, using actual integral PEL families, component
schemes, and finite etale correspondences. IntegralModel's geometric conclusions and
the good split-prime conditions are separate propositions. No Hecke action,
trace, flag classification, or convolution identity occurs in the record.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable (K : Type) [Field K] [NumberField K]

abbrev modelRing (d : ℕ) := Localization.Away (d : NumberField.RingOfIntegers K)
abbrev modelBase (d : ℕ) : Scheme := Spec (.of (modelRing K d))

def modelGeneric (d : ℕ) (hd : d ≠ 0) : Spec (.of K) ⟶ modelBase K d :=
  Spec.map (CommRingCat.ofHom (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K d hd))

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]

/-- Genuine PEL and Albanese candidates over a localized ring of integers,
and genuine generic-fiber correspondence covers. Existence and geometric
classification are not fields of this record. -/
structure SphericalPELAlbaneseData
    (E K : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] (s q : ℕ) [Fact q.Prime] where
  reference : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s
  fieldEmbedding : E →+* K
  complexEmbedding : K →+* ℂ
  level : ℕ
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  model : PELModuli.PELModuliCandidate reference level (modelBase K denominator)
  componentCount : ℕ
  components : PELModuli.IntegralModel.Components.ComponentAlbaneseData model.space componentCount
  inclusion : ∀ j, components.S j ⟶ model.space
  correspondence : Local.IntegralType s → Correspondences.EtaleCorrespondence
    ((Over.pullback (modelGeneric K denominator denominator_ne_zero)).obj model.space)
  localCharacter : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q]

namespace SphericalPELAlbaneseData

variable {E K} {s q : ℕ} [Fact q.Prime] (D : SphericalPELAlbaneseData E K s q)

abbrev generic := modelGeneric K D.denominator D.denominator_ne_zero
abbrev space := (Over.pullback D.generic).obj D.model.space

/-- The generic universal family is an actual pullback of the integral one. -/
abbrev family : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level D.space.left :=
  D.model.family.pullback (pullback.fst D.model.space.hom D.generic)

abbrev complexPoint : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ modelBase K D.denominator :=
  Spec.map (CommRingCat.ofHom D.complexEmbedding) ≫ D.generic

/-- The base action is induced by the number-field embedding on integers. -/
def baseAction : NumberField.RingOfIntegers E →+* Γ(modelBase K D.denominator, ⊤) :=
  (Scheme.ΓSpecIso (.of (modelRing K D.denominator))).inv.hom.comp
    ((algebraMap (NumberField.RingOfIntegers K) (modelRing K D.denominator)).comp
      (NumberField.RingOfIntegers.mapRingHom D.fieldEmbedding))

abbrev componentAssembly := Sigma.desc D.inclusion

/-- Exactly the geometric inputs supplied by IntegralModel, including the actual
Albanese universal properties, Betti map, and uniform fiberwise generation. -/
structure HasIntegralModelGeometry : Prop where
  reference_admissible : D.reference.IsAdmissible
  embedding : D.complexEmbedding.comp D.fieldEmbedding = D.reference.μ
  fullLevel : 3 ≤ D.level
  levelUnit : IsUnit (D.level : modelRing K D.denominator)
  classifies : D.model.ClassifiesReduced D.baseAction
  reduced : IsReduced D.model.space.left
  smooth : Smooth D.model.space.hom
  proper : IsProper D.model.space.hom
  projective : PELModuli.IntegralModel.Components.RelativelyProjective D.model.space
  decomposition : IsIso D.componentAssembly
  componentGeometry : ∀ j,
    Smooth (D.components.S j).hom ∧ IsProper (D.components.S j).hom ∧
      PELModuli.IntegralModel.Components.RelativelyProjective (D.components.S j) ∧
      GeometricallyConnected (D.components.S j).hom
  abelianGeometry : ∀ j,
    Smooth (D.components.A j).X.hom ∧ IsProper (D.components.A j).X.hom ∧
      GeometricallyConnected (D.components.A j).X.hom
  albanese : ∀ j, D.components.IsComplexAlbanese D.complexPoint j
  betti : letI := decomposition
    Function.Bijective (PELModuli.IntegralModel.Product.bettiPullbackQ
      (D.components.totalComplexMap D.complexPoint (asIso D.componentAssembly)) 1)
  generation : ∀ j, ∃ n : ℕ, 0 < n ∧
    ∀ t : PELModuli.IntegralModel.Base.GeometricPoint (modelBase K D.denominator),
      Function.Surjective (D.components.sumOfDifferences j n t)

/-- The product Albanese and its integral endomorphism ring are constructed
from the component group schemes, followed by actual base change to K. -/
abbrev albaneseGroup : CommGrp (Over (Spec (.of K))) :=
  BaseChange.baseChangedGroup (Products.componentProduct D.components.A).X D.generic
abbrev EndK := End.IntegralEnd D.albaneseGroup.X
abbrev EndQ := End.RationalEnd D.albaneseGroup.X
abbrev toRational := End.endToRational D.albaneseGroup.X

/-- The total Albanese map is assembled using the IntegralModel decomposition. -/
def albaneseMap (h : D.HasIntegralModelGeometry) : D.space ⟶ D.albaneseGroup.X := by
  let : IsIso D.componentAssembly := h.decomposition
  exact (Over.pullback D.generic).map
    (D.components.totalMap (asIso D.componentAssembly) ≫
      (Products.componentProductComparison D.components.A).inv)

/-- The completion map is built from the chosen integral local characters. -/
def localCompletionMap :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ] (Fin s × Bool → ℤ_[q]) :=
  Algebra.TensorProduct.lift
    (algebraMap ℤ_[q] (Fin s × Bool → ℤ_[q])).toIntAlgHom
    (RingHom.pi D.localCharacter).toIntAlgHom (fun _ _ => Commute.all _ _)

/-- Complete splitting is the actual product decomposition of the integral
completion. The same prime avoids level, polarization, and model denominators. -/
def IsGoodCompletelySplitPrime : Prop :=
  Function.Bijective D.localCompletionMap ∧
  (∀ (v : Fin s) (side : Bool) (a : NumberField.RingOfIntegers E),
    D.localCharacter (v, !side) a = D.localCharacter (v, side)
      (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ∧
  Nat.Coprime q D.level ∧ Nat.Coprime q D.denominator ∧
    Nat.Coprime q (∏ i, D.reference.polarizationType i)

/-- Neighbor multiplicity is derived from the actual finite source fiber. -/
abbrev neighbors (t : Local.IntegralType s) {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : Over.mk b ⟶ D.space) :=
  (D.correspondence t).neighbors b x

end SphericalPELAlbaneseData

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
