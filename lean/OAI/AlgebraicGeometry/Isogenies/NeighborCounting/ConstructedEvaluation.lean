import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LiftBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Reduction

/-! # Constructed Evaluation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-!
Connect the constructed evaluation DVR and parameter points to the
actual lifted PEL source and the independently evaluated neighbor targets.
All reductions use proper extension in the native moduli scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field L] [Algebra R L]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (v : EvaluationDVRLifts.EvaluationDVR R L)

section

variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

/-- The DVRLifting source lift over the constructed finite evaluation DVR. -/
def Lifts.IntegralLift.overEvaluationDVR :
    Lifts.IntegralLift D v.carrier ((algebraMap R v.carrier).comp b) (residueIso.trans v.residueIso) x :=
  l.baseChange (algebraMap R v.carrier) v.residueIso v.residue_compatible

/-- The source comparison preserves the actual normalized Poincare
bundle, positive polarization, and ordered marking under base change. -/
def Lifts.IntegralLift.evaluationPolarizedIso : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))))
    (l.overEvaluationDVR v).polarized :=
  AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp D.integral.universal.data.polarized l.map
    (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))

end

theorem ConstructedEvaluation.Lifts.evaluation_residueCompatible (hbase : Lifts.ResidueCompatible D R b residueIso) :
    Lifts.ResidueCompatible D v.carrier ((algebraMap R v.carrier).comp b)
      (residueIso.trans v.residueIso) :=
  LiftBaseChange.Lifts.residueCompatible_baseChange (algebraMap R v.carrier) v.residueIso v.residue_compatible hbase

section

/-- An evaluated generic map over the original arithmetic base becomes
an evaluated target over the constructed DVR, by its scalar-tower equation. -/
def Evaluated.Targets.Lifts.EvaluatedTarget.overEvaluationDVR (z : Spec (.of L) ⟶ D.integral.toOver.left)
    (hz : z ≫ D.integral.toOver.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Lifts.dvrBase R b) :
    Evaluated.Targets.Lifts.EvaluatedTarget D v.carrier L ((algebraMap R v.carrier).comp b) where
  map := z
  overBase := by
    rw [hz]
    change Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap R v.carrier).comp b))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact IsScalarTower.algebraMap_apply R v.carrier L (b a)

end

variable {L₀ : Type} [Field L₀] [Algebra R L₀]
variable {X : Over (Spec (.of L₀))} (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField L₀ X)
variable [Algebra R d.carrier] [IsScalarTower R L₀ d.carrier]
variable (v : EvaluationDVRLifts.EvaluationDVR R d.carrier)
variable (t : X.left ⟶ D.integral.toOver.left)
variable (ht : t ≫ D.integral.toOver.hom =
  X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R L₀)) ≫ Lifts.dvrBase R b)

include ht in
omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem ConstructedEvaluation.Lifts.parameterTarget_overBase (i : ULift (Fin d.count)) :
    (d.parameterPoint i ≫ t) ≫ D.integral.toOver.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R d.carrier)) ≫ Lifts.dvrBase R b := by
  rw [Category.assoc, ht, ← Category.assoc, d.parameterPoint_overBase]
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (IsScalarTower.algebraMap_apply R L₀ d.carrier r).symm)

/-- The neighbor family is evaluated by applying its original target map
to every point of its native parameter scheme. -/
def ConstructedEvaluation.Lifts.evaluatedParameterTargets :
    Multiset (Evaluated.Targets.Lifts.EvaluatedTarget D v.carrier d.carrier ((algebraMap R v.carrier).comp b)) :=
  Finset.univ.val.map (fun i => Evaluated.Targets.Lifts.EvaluatedTarget.overEvaluationDVR v (d.parameterPoint i ≫ t)
    (ConstructedEvaluation.Lifts.parameterTarget_overBase d t ht i))

/-- Proper reduction of the independently evaluated parameter targets;
there is no count-table or mixed-operator formula in this definition. -/
def ConstructedEvaluation.Lifts.reducedParameterTargets (hbase : Lifts.ResidueCompatible D R b residueIso) :
    Multiset D.GeometricPoint :=
  Evaluated.Reduction.Lifts.reduceToGeometricPoints D v.carrier d.carrier ((algebraMap R v.carrier).comp b)
    (residueIso.trans v.residueIso) (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (ConstructedEvaluation.Lifts.evaluatedParameterTargets d v t ht)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
