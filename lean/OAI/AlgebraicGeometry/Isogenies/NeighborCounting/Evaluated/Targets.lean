import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Targets -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-!
Evaluated generic targets extend to the actual proper integral PEL model.
Their reductions are defined from the unique extensions, independently of
any kernel-counting or operator identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section ProperExtension

universe u

variable {R L : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  (b : Spec (.of R) ⟶ S) (z : Spec (.of L) ⟶ X)
  (hz : z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ b)

include hz in
/-- Properness extends an evaluated point; separatedness makes the
extension unique. Neither its special fiber nor its kernel is specified. -/
theorem Evaluated.Targets.Lifts.proper_evaluated_extension :
    ∃! l : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l = z ∧ l ≫ f = b := by
  let sq : ValuativeCommSq f :=
    { R := R
      commRing := inferInstance
      domain := inferInstance
      valuationRing := inferInstance
      K := L
      field := inferInstance
      algebra := inferInstance
      isFractionRing := inferInstance
      i₁ := z
      i₂ := b
      commSq := ⟨hz⟩ }
  have H : ValuativeCriterion.Existence f :=
    ((congrFun (congrFun (congrFun UniversallyClosed.eq_valuativeCriterion X) S) f).mp
      (inferInstance : UniversallyClosed f)).1
  obtain ⟨l, hl, hb⟩ := (H sq).exists_lift
  refine ⟨l, ⟨hl, hb⟩, ?_⟩
  intro m hm
  have : Subsingleton sq.commSq.LiftStruct := IsSeparated.valuativeCriterion f sq
  let lm : sq.commSq.LiftStruct := ⟨m, hm.1, hm.2⟩
  let ll : sq.commSq.LiftStruct := ⟨l, hl, hb⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim lm ll)

end ProperExtension

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable (b : B.R →+* R)

/-- An individually evaluated generic moduli point over the DVR fraction
field. The arithmetic square is the only condition in this definition. -/
structure Evaluated.Targets.Lifts.EvaluatedTarget where
  map : Spec (.of L) ⟶ D.integral.toOver.left
  overBase : map ≫ D.integral.toOver.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Lifts.dvrBase R b

namespace Evaluated.Targets.Lifts.EvaluatedTarget

variable {D R L b} (z : EvaluatedTarget D R L b)

def extension : Spec (.of R) ⟶ D.integral.toOver.left :=
  (proper_evaluated_extension D.integral.toOver.hom (Lifts.dvrBase R b) z.map z.overBase).choose

theorem extension_generic :
    Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ z.extension = z.map :=
  (proper_evaluated_extension D.integral.toOver.hom (Lifts.dvrBase R b) z.map z.overBase).choose_spec.1.1

theorem extension_overBase : z.extension ≫ D.integral.toOver.hom = Lifts.dvrBase R b :=
  (proper_evaluated_extension D.integral.toOver.hom (Lifts.dvrBase R b) z.map z.overBase).choose_spec.1.2

theorem extension_unique (l : Spec (.of R) ⟶ D.integral.toOver.left)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l = z.map)
    (hb : l ≫ D.integral.toOver.hom = Lifts.dvrBase R b) : l = z.extension :=
  (proper_evaluated_extension D.integral.toOver.hom (Lifts.dvrBase R b) z.map z.overBase).choose_spec.2
    l ⟨hl, hb⟩

def reduction : Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.integral.toOver.left :=
  Lifts.closedBase R ≫ z.extension

def polarized : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of R)) :=
  D.integral.universal.data.polarized.pullback z.extension

def action : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) z.polarized.abelian :=
  D.integral.universal.data.action.pullback z.extension

/-- The evaluated generic fiber includes the actual normalized Poincare
bundle, positive polarization, and ordered marking. -/
def genericPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (z.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (D.integral.universal.data.polarized.pullback z.map) := by
  have e := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized
    z.extension (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  rw [z.extension_generic] at e
  exact e

def specialPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (z.polarized.pullback (Lifts.closedBase R))
    (D.integral.universal.data.polarized.pullback z.reduction) :=
  AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized
    z.extension (Lifts.closedBase R)

end Evaluated.Targets.Lifts.EvaluatedTarget

/-- Reduce each independently evaluated generic target, retaining repeated
targets with their multiplicities. This definition has no count formula. -/
def Evaluated.Targets.Lifts.reduceEvaluatedTargets (neighbors : Multiset (Evaluated.Targets.Lifts.EvaluatedTarget D R L b)) :
    Multiset (Spec (.of (IsLocalRing.ResidueField R)) ⟶ D.integral.toOver.left) :=
  neighbors.map Evaluated.Targets.Lifts.EvaluatedTarget.reduction

variable {D R b} [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R} {x : D.GeometricPoint}
  (l : Lifts.IntegralLift D R b residueIso x)

def Lifts.IntegralLift.specialPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (l.polarized.pullback (Lifts.closedBase R))
    (D.integral.universal.data.polarized.pullback (Lifts.residuePoint D R residueIso x)) := by
  have e := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized
    l.map (Lifts.closedBase R)
  rw [l.reduction] at e
  exact e

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
