import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily

/-! # Active Parameter Family -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.Family

/-! The constructed generic active family is the inverse image of the
actual integral active family under the evaluated source comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion.Square
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L)
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (((l.action).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 (labels (0, false))))))

variable (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))

def evaluatedGenericActiveParameterIdentity :=
  PLift.up (TransportedKernelParameterFamily.Family.transportedKernel_parameter_family
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _ _ _
    (PrimeBlockInclusion.Square.evaluatedOriginalPrimeInclusion (F := F) j hsplit l (labels (0, false)))
    (PrimeBlockInclusion.Square.evaluatedIntegralPrimeInclusion j hsplit l v (labels (0, false)))
    (PrimeBlockComparison.evaluatedPrimeBlockGroupIso (F := F) j hsplit l v (labels (0, false)))
    (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v)
    (ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J)
    (PrimeBlockInclusion.Square.evaluatedPrimeBlockGroupIso_square j hsplit l v (labels (0, false))))

theorem evaluatedGenericActiveKernel_parameter_family :
    type_of% (evaluatedGenericActiveParameterIdentity j hsplit labels O l v eA J).down :=
  (evaluatedGenericActiveParameterIdentity j hsplit labels O l v eA J).down

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.Family

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.SourceFamilies

/-! Both actual active families are named in the original generic ambient group, so their comparison has a source type independent of the evaluation DVR. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericActiveKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelParameterFamily.Family
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion.Square
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L)
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (((l.action).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 (labels (0, false))))))

variable (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q))

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.Family

abbrev evaluatedOriginalAmbientGroup : Grp (Over (Spec (.of L))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.obj
    (Grp.mk (l.polarized.abelian.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme)

def evaluatedIntegralActiveSourceFamily :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (evaluatedOriginalAmbientGroup (F := F) (L := L) l).X
      (Over.mk (𝟙 (Spec (.of L)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))
  let H := ActiveCoordinateEquiv.evaluatedActiveIntegralKernel j hsplit labels O l v eA J
  let i := H.inclusion ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
    ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 (labels (0, false))))
  let family := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (l.overEvaluationDVR v).polarized.abelian.scheme)
    (Over.mk g) (Kernel.Base.fixedKernelFamily i)
  let result := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
    (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom family
  exact result

def evaluatedGenericActiveSourceFamily :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (evaluatedOriginalAmbientGroup (F := F) (L := L) l).X
      (Over.mk (𝟙 (Spec (.of L)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let H := GenericActiveKernel.evaluatedGenericActiveKernel j hsplit labels O l v eA J
  let i := H.inclusion ≫ (Over.pullback f).map
    (PrimeBlockInclusion.Square.evaluatedOriginalPrimeInclusion (F := F) j hsplit l (labels (0, false))).hom.hom
  let result := Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of L)))) i
  exact result

theorem evaluatedActiveSourceFamilies_eq :
    evaluatedIntegralActiveSourceFamily j hsplit labels O l v eA J =
      evaluatedGenericActiveSourceFamily j hsplit labels O l v eA J :=
  Family.evaluatedGenericActiveKernel_parameter_family j hsplit labels O l v eA J

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.SourceFamilies

end

end OAI
