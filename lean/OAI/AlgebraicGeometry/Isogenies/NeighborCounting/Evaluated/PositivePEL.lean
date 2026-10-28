import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositiveNeighbors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldIntegralPEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.IntegralPEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntrinsicPoincareBundlePEL

/-! # Positive PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositivePEL

noncomputable section

/-! Construct the original evaluated neighbor's integral PEL object and
full PEL isogeny. Its source is the exact original source in the NeighborCounting
specification, with every parameter and full kernel retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelModels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.AbelianNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CanonicalIsotropy OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldIntegralPEL
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

private theorem mapIdentity_comp_identity {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    (F : C₀ ⥤ C₁) (X : C₀) {Y : C₁} (f : F.obj X ⟶ Y) :
    F.map (𝟙 X) ≫ f ≫ 𝟙 Y = f := by
  rw [F.map_id, Category.id_comp, Category.comp_id]

private theorem prescribedKernel_of_hom_eq {S : Scheme.{0}} {A B H : Over S} [GrpObj B]
    (f g : A ⟶ B) (i : H ⟶ A) (h : f = g) (hg : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel g i) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f i := h.symm ▸ hg

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (active : Fin s) (multiplicative : Fin s → Bool)
variable (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents active multiplicative i v) (HeckeExponents.neighborExponents_bound active multiplicative i v)

local instance chosenProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inl v)))

local instance oppositeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inr v)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

variable (hlabels : ∀ v, labels (Sum.swap v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels v)

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

def evaluatedNeighborIntegralObject :=
  ModeledFieldIntegralPEL.modeledFieldIntegralPEL (l.genericIntegralObject (L := L))
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (D.polarizationPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (CanonicalIsotropy.evaluatedCompleteKernel_self_annihilating j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (AbelianNeighbors.evaluatedCompleteKernel_stable j hsplit labels active multiplicative h_TorsionQuotient l d i a)

def evaluatedNeighborModelPELIsogeny :=
  IntrinsicPoincareBundlePEL.ModeledIntrinsic.modeledNativePoincareBundlePELIsogeny (l.genericIntegralObject (L := L)).data
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    q (HeckeExponents.neighborLevel i) (Fact.out : q.Prime)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    D.polarizationPrimeToQ
    (CanonicalIsotropy.evaluatedCompleteKernel_self_annihilating j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (AbelianNeighbors.evaluatedCompleteKernel_stable j hsplit labels active multiplicative h_TorsionQuotient l d i a)

def evaluatedNeighborPELIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
      ((Intrinsic.ReductionSpecification.genericSource (L := L) l).pullback (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom)
      (ActionFamilyComparison.Family.actionFamily (evaluatedNeighborIntegralObject j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a).data)
      (q ^ HeckeExponents.neighborLevel i) :=
  (evaluatedNeighborModelPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a).transport
    ((ActionFamilyComparison.Family.actionFamilyPullbackIso l.actionData (Spec.map (CommRingCat.ofHom (algebraMap R L)))).pullback
      (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom)
    (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _)

omit [IsFractionRing R L] in
theorem evaluatedNeighborPELIsogeny_hom :
    (evaluatedNeighborPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a).isogeny.hom =
      (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).isogeny.hom := by
  have ht := AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom
    (evaluatedNeighborModelPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    ((ActionFamilyComparison.Family.actionFamilyPullbackIso l.actionData (Spec.map (CommRingCat.ofHom (algebraMap R L)))).pullback
      (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom)
    (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _)
  apply ht.trans
  change (Over.pullback (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom).map (𝟙 _) ≫
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).isogeny.hom ≫ 𝟙 _ = _
  exact mapIdentity_comp_identity
    (Over.pullback (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom) _
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).isogeny.hom

omit [IsFractionRing R L] in
theorem evaluatedNeighborPELIsogeny_kernel :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (evaluatedNeighborPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a).isogeny.hom
      (AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion (l.genericPolarized (L := L)).abelian
        (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d)
        (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
        (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)) := by
  exact prescribedKernel_of_hom_eq _ _ _
    (evaluatedNeighborPELIsogeny_hom j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).kernel

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositivePEL
