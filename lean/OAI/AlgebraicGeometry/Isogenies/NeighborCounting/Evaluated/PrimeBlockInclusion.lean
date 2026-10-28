import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison

/-! # Prime Block Inclusion -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion

/-! The literal original q-block retains its ambient inclusion under
its constructed comparison with the evaluated integral q¹-block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L) (τ : Gal(E/ℚ))

theorem evaluatedPrimeBlockGroupIso_inclusion :
    (PrimeBlockComparison.evaluatedPrimeBlockGroupIso (F := F) j hsplit l v τ).hom.hom.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
          ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 τ))) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q
          ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
            (j.projector iota hsplit 1 τ))) ≫
      (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom.hom.hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap F L))
  let g := Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))
  let p := (l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
    (j.projector iota hsplit 1 τ)
  let e₀ : AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q p ≅ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) p :=
    (Grp.forget _).mapIso (Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso.nativeBlockLevelGroupIso q (q ^ 1) p (pow_one q).symm)
  let e₁ : (Over.pullback f).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) p) ≅
      (Over.pullback g).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
        ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 τ))) :=
    (Grp.forget _).mapIso (BlockPointComparison.evaluatedLiftGenericBlockGroupIso (F := F) j hsplit l v 1 τ)
  let a : (Over.pullback f).obj (l.polarized.abelian.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme ≅
      (Over.pullback g).obj (l.overEvaluationDVR v).polarized.abelian.scheme :=
    (Grp.forget _).mapIso (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v)
  have he : e₁.hom ≫ (Over.pullback g).map
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
        ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 τ))) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) p) ≫ a.hom :=
    GenericBlockInclusion.evaluatedLiftGenericBlockGroupIso_inclusion j hsplit l v 1 τ
  have h₀ : e₀.hom ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) p = AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q p :=
    Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso.nativeBlockLevelGroupIso_inclusion q (q ^ 1) p (pow_one q).symm
  change ((Over.pullback f).map e₀.hom ≫ e₁.hom) ≫ _ =
    (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q p) ≫ a.hom
  have hm : (Over.pullback f).map e₀.hom ≫
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) p) =
      (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q p) :=
    ((Over.pullback f).map_comp _ _).symm.trans
      (congrArg (fun z => (Over.pullback f).map z) h₀)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Over.pullback f).map e₀.hom ≫ z) he).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ a.hom) hm)))

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion.Square

/-! The actual original and integral prime-block inclusions form a
commuting square of group-scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L) (τ : Gal(E/ℚ))

def evaluatedOriginalPrimeInclusion :
    Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q
      ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 τ))) ⟶
      Grp.mk (l.polarized.abelian.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).scheme :=
  Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q
    ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
      (j.projector iota hsplit 1 τ)))

def evaluatedIntegralPrimeInclusion :
    Lifted.GeometricBlockIso.nativeActionBlockGroup (l.overEvaluationDVR v).polarized.abelian
      (l.overEvaluationDVR v).action (q ^ 1) (j.projector iota hsplit 1 τ) ⟶
    Grp.mk (l.overEvaluationDVR v).polarized.abelian.scheme := by
  let i := Grp.ofHom (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
    ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 τ)))
  exact i

theorem evaluatedPrimeBlockGroupIso_square :
    (PrimeBlockComparison.evaluatedPrimeBlockGroupIso (F := F) j hsplit l v τ).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L)))).mapGrp.map
        (evaluatedIntegralPrimeInclusion j hsplit l v τ) =
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.map
        (evaluatedOriginalPrimeInclusion (F := F) j hsplit l τ) ≫
      (SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := F) l v).hom := by
  apply Grp.hom_ext
  exact evaluatedPrimeBlockGroupIso_inclusion (F := F) j hsplit l v τ

end AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockInclusion.Square

end

end OAI
