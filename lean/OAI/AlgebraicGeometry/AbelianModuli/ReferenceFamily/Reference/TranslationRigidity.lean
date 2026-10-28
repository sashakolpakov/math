import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.Translation
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge

/-! # Translation Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! An algebraic translation preserving the primitive reference theta
bundle lies in the original integral dual lattice. This identifies the
translation kernel from actual line-bundle isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

section

theorem Fiber.ReferenceAnalyticFiber.translationGauge_mem_dual (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (a : Fiber.ReferenceTangent s) (c : Fiber.ReferenceTangent s → ℂ) (hc : Differentiable ℂ c) (hc0 : c 0 ≠ 0)
    (htrans : ∀ (l : P.lattice) w, c (w + F.latticeEmbedding l) * F.polarizationAutomorphy hP l (w + a) =
      F.polarizationAutomorphy hP l w * c w) : a ∈ F.dualLattice := by
  let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice) := F.compact
  have hshift : ∀ (l : F.lattice) w, RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge F.form a c (w + l.val) =
      RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter F.form a l.val * RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge F.form a c w := by
    intro l w
    let m := F.integralLatticeEquiv.symm l
    have hm : F.latticeEmbedding m = l.val := F.latticeEmbedding_symm l
    have H := RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge_translates (P.referenceBasis hP) P.integralForm
      F.latticeEmbedding F.form a c htrans m w
    rw [hm] at H
    exact H
  intro v hv
  have hχ := RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity.unitaryAutomorphy_trivial F.lattice (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge F.form a c)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter F.form a m.val)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_unitary _ F.hermitian a m.val)
    (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge_differentiable _ a c hc) hshift
    (by simpa [RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge] using hc0) ⟨v, hv⟩
  obtain ⟨m, hm⟩ := (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_eq_one_iff _ F.hermitian a v).mp hχ
  exact Submodule.mem_one.mpr ⟨m, hm.symm⟩

end

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

theorem AlgebraicModel.ReferenceAlgebraicModel.nativeTranslation_mem_dual (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (a : Fiber.ReferenceTangent s)
    (u : ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback
      (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk a))).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf) : a ∈ F.dualLattice := by
  obtain ⟨c, hc, hcn, htrans⟩ := RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge.exists_holomorphic_translationGauge_of_native_iso U V hdeg
    M.abelian M.period M.period_add f g hf hg a u
  apply F.translationGauge_mem_dual hP a c hc (hcn 0)
  intro l w
  have H := htrans (F.integralLatticeEquiv l) w
  change c (w + F.latticeEmbedding l) *
      F.polarizationAutomorphy hP (F.integralLatticeEquiv.symm (F.integralLatticeEquiv l)) (w + a) =
    F.polarizationAutomorphy hP (F.integralLatticeEquiv.symm (F.integralLatticeEquiv l)) w * c w at H
  simpa only [LinearEquiv.symm_apply_apply] using H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
