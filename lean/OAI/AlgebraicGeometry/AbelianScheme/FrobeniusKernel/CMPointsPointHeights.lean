import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightFieldBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataHeightTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointSourceComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints

/-! # CM Points Point Heights -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsPointHeights.Construction

noncomputable section

/-! Transport CMPoints's full height witnesses to the original fixed-field
point datum. The field map and polarized action isomorphism are the
constructed comparisons of the original universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section Fields

variable {k k' O : Type} [Field k] [Field k'] [CommRing O]
variable {g q : ℕ} [Fact q.Prime]
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
variable (χ : O →+* PadicInt q) (f : k →+* k') {h : ℕ}

theorem l45BlockHasHeight_ringHomBaseChange (hA : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ χ h) :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (A.pullback (Spec.map (CommRingCat.ofHom f)))
      (ρ.pullback (Spec.map (CommRingCat.ofHom f))) χ h := by
  let : Algebra k k' := f.toAlgebra
  exact HeightFieldBaseChange.Construction.l45BlockHasHeight_fieldBaseChange (k' := k') A ρ χ hA

end Fields

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j) (a : M.Family)
variable (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a) (τ : Gal(E/ℚ)) (r : ℕ)
variable (hr : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight
  (R.fiberAbelian a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x))
  (R.fiberAction a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x))
  (j.localCharacter M.extendedEmbedding τ) r)

include hr in
theorem l45TransportedFiber_hasBlockHeight :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight
      ((PointsGeometricPointData.Construction.l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
        (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom)).polarized.abelian
      ((PointsGeometricPointData.Construction.l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
        (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom)).action
      (j.localCharacter M.extendedEmbedding τ) r :=
  l45BlockHasHeight_ringHomBaseChange _ _ (j.localCharacter M.extendedEmbedding τ)
    (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom.hom hr

include hr in
theorem l45FixedPoint_hasBlockHeight :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
      (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action (j.localCharacter M.extendedEmbedding τ) r :=
  ActionDataHeightTransport.Construction.polarizedActionIso_hasBlockHeight (PointsGeometricPointData.Construction.l45GeometricPointDataIso M R a x)
    (j.localCharacter M.extendedEmbedding τ) r (l45TransportedFiber_hasBlockHeight M R a x τ r hr)

theorem l45GeometricConclusion_fixedHeights (h : CMPoints.Construction.GeometricConclusion R) :
    ∀ (a : M.Family) (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a) (τ : Gal(E/ℚ)),
      PELModuli.CMPoints.BlocksProjectors.BlockHasHeight (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
        (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action (j.localCharacter M.extendedEmbedding τ) 3 := by
  obtain ⟨_, _, _, hheight, _⟩ := h.2
  intro a x τ
  exact l45FixedPoint_hasBlockHeight M R a x τ 3
    (hheight a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x) τ).1

variable (hM : M.HasPrescribedBallPeriods)
variable (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
variable (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ (v : Fin M.s) (b : Bool),
  labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))

include hr in
theorem l45PointDatum_hasBlockHeight :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight
      ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data.polarized.abelian
      ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data.action
      (j.localCharacter M.extendedEmbedding τ) r :=
  l45FixedPoint_hasBlockHeight M R a x τ r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsPointHeights.Construction
