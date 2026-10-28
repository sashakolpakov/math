import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.KernelParameters
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveAmbientComparisonData
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage

/-! # Active Kernel Image -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.ActiveKernelImage

noncomputable section

/-! The active integral kernel has the unchanged original active choice as its generic image in the abelian source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.KernelParameters OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage
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

variable {I : Type} [Finite I]
  (split : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of d.carrier)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))))
  (a : ULift (Fin (d.count (some i))))

local instance pulledBackInclusion :
    IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))).map
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)))) :=
  Functor.map.instIsMonHom
    (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))))
    (f := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ))) _ _

include split in
theorem jointActiveKernel_image_eq :
    let Q := KernelParameters.jointKernelParameters j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates C
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of d.carrier))))
      ((C.kernel (Q.enumeration a).val).inclusion ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))).map
          (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)))) =
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme)
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))))
      (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup := by
  let Q := KernelParameters.jointKernelParameters j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates C
  let g : Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) ⟶ Grp.mk A.scheme :=
    Grp.homMk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)))
  exact (Q.image_kernel_eq split g a).trans
    (congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme)
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))))
      (Evaluated.ActiveChoiceImage.evaluatedPrimeActiveSubgroup_image j iota hsplit A ρ c p hTorsionQuotient d i τ hp a))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.ActiveKernelImage
