import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.EvaluationDVR
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly

/-! # Hecke Evaluation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation

noncomputable section

/-! Construct the three actual elementary-type parameter schemes and
one finite field splitting them together with the source q-torsion.
The parameter functors retain the complete chosen-block tuple; active
coordinates have exponent one and compact coordinates have exponent i. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents

variable {K : Type} [Field K] [CharZero K] {d s : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of K))) (q : ℕ) [Fact q.Prime]
variable (active : Fin s) (multiplicative : Fin s → Bool)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents active multiplicative i v)
    (HeckeExponents.neighborExponents_bound active multiplicative i v)

variable (projectors : Fin 3 → Fin s → (A.scheme ⟶ A.scheme))
variable [∀ i v, IsMonHom (projectors i v)]

def neighborChoiceFunctor (i : Fin 3) : (Over (Spec (.of K)))ᵒᵖ ⥤ Type 1 :=
  AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor A.scheme (q ^ HeckeExponents.neighborLevel i)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v)) (projectors i v))

structure NativeNeighborParameter (i : Fin 3) where
  parameter : Over (Spec (.of K))
  [finite : IsFinite parameter.hom]
  [etale : Etale parameter.hom]
  represents : (neighborChoiceFunctor A q active multiplicative projectors i).RepresentableBy parameter

attribute [instance] NativeNeighborParameter.finite NativeNeighborParameter.etale

variable (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

def nativeNeighborParameter (i : Fin 3) : NativeNeighborParameter A q active multiplicative projectors i :=
  Classical.choice (show Nonempty (NativeNeighborParameter A q active multiplicative projectors i) from by
    obtain ⟨X, hf, he, ⟨repr⟩⟩ := AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.integral_block_parameters_from_TorsionQuotient
      (𝟙 (Spec (.of K))) A.scheme q (Fact.out : q.Prime) (HeckeExponents.neighborLevel i) s
      (HeckeExponents.neighborExponents active multiplicative i) (HeckeExponents.neighborExponents_bound active multiplicative i)
      (projectors i) h_TorsionQuotient
    exact ⟨{parameter := X, finite := hf, etale := he, represents := repr}⟩)

def neighborEvaluationSchemes : Option (Fin 3) → Over (Spec (.of K))
  | none => AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme q
  | some i => (nativeNeighborParameter A q active multiplicative projectors h_TorsionQuotient i).parameter

/-- One constructed finite extension splits all three independently
represented IsogenyQuotient families and the original source q-torsion. -/
def nativeHeckeEvaluation :
    Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField K (neighborEvaluationSchemes A q active multiplicative projectors h_TorsionQuotient) := by
  have ht := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A.scheme q
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of K))) q
      (Fact.out : q.Prime).pos h_TorsionQuotient)
  letI : ∀ i, IsFinite (neighborEvaluationSchemes A q active multiplicative projectors h_TorsionQuotient i).hom :=
    fun i => by cases i with
      | none => exact ht.1
      | some i => exact (nativeNeighborParameter A q active multiplicative projectors h_TorsionQuotient i).finite
  letI : ∀ i, Etale (neighborEvaluationSchemes A q active multiplicative projectors h_TorsionQuotient i).hom :=
    fun i => by cases i with
      | none => exact ht.2
      | some i => exact (nativeNeighborParameter A q active multiplicative projectors h_TorsionQuotient i).etale
  exact Joint.IntrinsicEvaluation.Lifts.jointFiniteEvaluationField K _

def evaluatedNeighborFamily (i : Fin 3) : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K
    (nativeNeighborParameter A q active multiplicative projectors h_TorsionQuotient i).parameter :=
  (nativeHeckeEvaluation A q active multiplicative projectors h_TorsionQuotient).family (some i)

def evaluatedSourceTorsion : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme q) :=
  (nativeHeckeEvaluation A q active multiplicative projectors h_TorsionQuotient).family none

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
