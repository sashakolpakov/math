import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateKernelDetection

/-! # Kernel Parameters -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.KernelParameters

noncomputable section

/-! Attach the actual original subgroup models before specializing the coordinate data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateMembership OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.RationalMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateMapValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (d : IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q 0 (Fin.cases false c) p hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)
  (τ : Gal(E/ℚ)) (hp : p i 0 = ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))
  (coordinates : ∀ v : Fin s,
    Additive ((d.family (some i)).extendedParameterBase k φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v.succ)) ≃+ (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable (C : GenericActiveCoordinateData.ActiveCoordinateData
  (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))
  (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ)))) q)

def jointKernelParameters :=
  let Q := CoordinateData.jointCoordinateData j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp
    coordinates C.coordinates.toAddEquiv
  show CoordinateKernelDetection.Parameters.CoordinateKernelParameters C (HeckeExponents.neighborLevel i)
    (ULift (Fin (d.count (some i))))
    (fun a => Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroup j iota hsplit A ρ c p hTorsionQuotient d i τ a) from {
      enumeration := Q.val
      membership := Q.property.2
      model := fun a => Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroupModel j iota hsplit A ρ c p hTorsionQuotient d i τ hp a }

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.KernelParameters
