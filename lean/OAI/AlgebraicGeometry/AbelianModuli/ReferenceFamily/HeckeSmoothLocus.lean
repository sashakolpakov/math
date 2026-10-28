import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSmooth
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedHeckeRealization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELPointClassification
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying

/-! # Hecke Smooth Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeSmoothLocus

noncomputable section

/-! The actual paired PEL quotients preserve smoothness of their two original
complex moduli points. The finite étale Hecke projections are base changed
along the given embedding, without changing either classifying map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine) (κ : K →+* ℂ)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) (hn : 0 < n) (hcop : Nat.Coprime n N) (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))

local instance : LocallyOfFinitePresentation (Z.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Limits.pullback.snd Z.space.hom (Spec.map (CommRingCat.ofHom κ))))

include hN hn hcop hmod hdegree in
theorem geometric_pair_complexPoints_mem_smoothLocus_iff
    {A B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))}
    (f : Paired.PELQuotients.PairedPELQuotient A B n) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying
        ((Z.complexPointBaseEquiv κ).symm (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ A)) ∈
        (Z.complexFiber κ).hom.smoothLocus ↔
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying
        ((Z.complexPointBaseEquiv κ).symm (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ B)) ∈
        (Z.complexFiber κ).hom.smoothLocus := by
  obtain ⟨R, _, het, u, _, hsource, htarget⟩ :=
    Geometric.PairedHeckeRealization.geometric_pair_realized_by_finite_etale_hecke Z hZ hN hn hcop hmod hdegree f
  have : Etale (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter).left := R.etale
  have : Etale (R.targetProjection Z hZ).left := het
  have h := EtaleSmooth.EtaleSmoothLocus.baseChangePoint_mem_smoothLocus_iff_of_etale_span
    (Spec.map (CommRingCat.ofHom κ)) (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter)
    (R.targetProjection Z hZ) u AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint
  rw [hsource, htarget] at h
  exact h

include hZ hN hn hcop hmod hdegree in
/-- Smoothness agrees at the original points whenever their universal fibers
are related by an actual paired PEL quotient of the prescribed degree. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.pairedQuotient_complexPoints_mem_smoothLocus_iff
    (x y : Z.ComplexPoints κ)
    (f : Paired.PELQuotients.PairedPELQuotient
      (Z.universal.pullback (Z.complexPointBaseEquiv κ x))
      (Z.universal.pullback (Z.complexPointBaseEquiv κ y)) n) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (Z.complexFiber κ).hom.smoothLocus ↔
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y ∈ (Z.complexFiber κ).hom.smoothLocus := by
  have h := geometric_pair_complexPoints_mem_smoothLocus_iff Z hZ κ hN hn hcop hmod hdegree f
  have hx : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ
      (Z.universal.pullback (Z.complexPointBaseEquiv κ x)) = Z.complexPointBaseEquiv κ x :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique Z hZ _ (Z.complexPointBaseEquiv κ x)
      ⟨Models.PELPullbackIso.canonical Z.universal (Z.complexPointBaseEquiv κ x)⟩).symm
  have hy : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ
      (Z.universal.pullback (Z.complexPointBaseEquiv κ y)) = Z.complexPointBaseEquiv κ y :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique Z hZ _ (Z.complexPointBaseEquiv κ y)
      ⟨Models.PELPullbackIso.canonical Z.universal (Z.complexPointBaseEquiv κ y)⟩).symm
  simpa only [hx, hy, Equiv.symm_apply_apply] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeSmoothLocus
