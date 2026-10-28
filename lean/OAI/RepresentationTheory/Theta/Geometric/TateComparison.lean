import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Tate Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.TateComparison

noncomputable section

/-! Exact, explicit prerequisite from TateComparison. Its entire conclusion is retained;
no active-block, period, or theta covariance assertion is added to it. This
module imports the implemented interface, never the admitted statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def TateComparisonOutput
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient) : Prop :=
    -- All geometric flags have ordinary chosen-block lattice realizations;
    -- opposite lattices, composite polarizations, and markings agree.
    D.HasPolarizedFlagRealizations hcorrespondences ∧

    ∃ (basis : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s → AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
      (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
      (markingShift : D.space ≅ D.space),

      -- The basis and its coefficients have their actual raw convolution meaning.
      (∀ t, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t)) ∧
      (∀ u v : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s,
        basis u.val * basis v.val =
          (coeff u v).sum (fun w n => n • basis w.val)) ∧
      (∀ (u v : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        (D.neighbors u b x).bind (D.neighbors v b) =
          (coeff u v).sum (fun w n => n • D.neighbors w b x)) ∧

      -- The central isogeny is [q] with the transported prime-to-q marking.
      D.CentralIsMultiplicationByQ hcorrespondences hgood.2.2.1 ∧
      D.IsCentralGraph markingShift ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        D.neighbors (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s) b x = {x ≫ markingShift.hom}) ∧

      -- Central shifts clear arbitrary chosen and opposite exponents.
      (∀ t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s, ∃ (n : ℕ) (u : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s),
        basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s) ^ n * basis t = basis u.val) ∧

      ∃ (TAlb : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → D.EndK)
        (ρ : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
        (ρH1 : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1),

        (∀ t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧

        -- Actual homomorphisms over K act by point push on component differences.
        (∀ (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
            (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
            (x y : Over.mk b ⟶ D.componentGeneric j),
          D.endPoint (TAlb t) (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
            ((D.neighbors t b (x ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum -
            ((D.neighbors t b (y ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum) ∧

        (∀ u v : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s,
          TAlb u * TAlb v = (coeff u v).sum (fun w n => n • TAlb w)) ∧
        IsUnit (ρ (basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s))) ∧

        -- Pullback on actual rational Betti H1, including rational endomorphisms.
        (∀ h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q, D.IsRationalH1Pullback (ρ h) (ρH1 h)) ∧

        -- Pullback on one-forms equals the actual sum over target branches.
        (∀ (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
          AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t)
            (D.albanesePullback hgeometry ω)
            (D.albanesePullback hgeometry (D.pullbackForms (TAlb t) ω)))

def TateComparisonInput : Prop :=
  ∀ {E K : Type}
    [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (_hs : 0 < s) (_hdegree : Module.finrank ℚ E = 2 * s)
    (q : ℕ) [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient)
    (_hE07 : AlgebraicGeometry.PELModuli.IntegralModel.Albanese.ConstructionInput) (_hE46 : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]),
    TateComparisonOutput D hgeometry hgood hcorrespondences

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

/-- Candidate operators of the supplied TateComparison theorem. This record contains
no realization proofs and no active-block or theta assertions. -/
structure Action where
  basis : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s → AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q
  shift : D.space ≅ D.space
  integral : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → D.EndK
  algebraAction : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ
  cohomologyAction : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1

variable (A : Action D) (hg : D.HasIntegralModelGeometry)
  (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

/-- Only TateComparison's already supplied conclusions, projected from its complete
output. In particular, branch formulas here are on actual affine splittings. -/
structure Action.IsRealization : Prop where
  flags : D.HasPolarizedFlagRealizations hIsogenyQuotient
  basis : ∀ t, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q t) (A.basis t)
  central : D.CentralIsMultiplicationByQ hIsogenyQuotient hq.2.2.1
  graph : D.IsCentralGraph A.shift
  integral : ∀ t, D.toRational (A.integral t) = A.algebraAction (A.basis t.val)
  centralUnit : IsUnit (A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)))
  pointPush : ∀ (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
    (x y : Over.mk b ⟶ D.componentGeneric j),
    D.endPoint (A.integral t) (D.aPoint hg j x - D.aPoint hg j y) =
      ((D.neighbors t b (x ≫ D.componentInclusion j)).map (D.aTotalPoint hg)).sum -
      ((D.neighbors t b (y ≫ D.componentInclusion j)).map (D.aTotalPoint hg)).sum
  cohomology : ∀ h, D.IsRationalH1Pullback (A.algebraAction h) (A.cohomologyAction h)
  forms : ∀ t ω, AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t)
    (D.albanesePullback hg ω) (D.albanesePullback hg (D.pullbackForms (A.integral t) ω))

theorem TateComparisonOutput.produces_action (h : TateComparisonOutput D hg hq hIsogenyQuotient) :
    ∃ A : Action D, A.IsRealization D hg hq hIsogenyQuotient := by
  obtain ⟨hflags, basis, coeff, shift, hbasis, _, _, hcentral, hgraph, _, _,
    integral, rho, rhoH1, hint, hpush, _, hunit, hH1, hforms⟩ := h
  refine ⟨⟨basis, shift, integral, rho, rhoH1⟩, ?_⟩
  exact ⟨hflags, hbasis, hcentral, hgraph, hint, hunit, hpush, hH1, hforms⟩

end

end OAI.RepresentationTheory.Theta.Geometric.TateComparison
