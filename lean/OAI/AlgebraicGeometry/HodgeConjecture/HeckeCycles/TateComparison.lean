import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Tate Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM

noncomputable section

/-! The complete TateComparison proposition, supplied as an explicit named input.
No theorem stub is used. Its compiled type is compared separately in
HeckeCyclesTateComparisonInputAudit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def TateComparisonInput : Prop := ∀
    {E K : Type}
    [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (_hs : 0 < s)
    (_hdegree : Module.finrank ℚ E = 2 * s)
    (q : ℕ) [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient)
    (_hE07 : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (_hE46 : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]),
    -- All geometric flags have ordinary chosen-block lattice realizations;
    -- opposite lattices, composite polarizations, and markings agree.
    D.HasPolarizedFlagRealizations hcorrespondences ∧

    ∃ (basis : AbelianScheme.TateComparison.Local.LocalType s → AbelianScheme.TateComparison.HeckeKernel.Hecke s q)
      (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
      (markingShift : D.space ≅ D.space),

      -- The basis and its coefficients have their actual raw convolution meaning.
      (∀ t, AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.HeckeKernel.representative s q t) (basis t)) ∧
      (∀ u v : AbelianScheme.TateComparison.Local.IntegralType s,
        basis u.val * basis v.val =
          (coeff u v).sum (fun w n => n • basis w.val)) ∧
      (∀ (u v : AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        (D.neighbors u b x).bind (D.neighbors v b) =
          (coeff u v).sum (fun w n => n • D.neighbors w b x)) ∧

      -- The central isogeny is [q] with the transported prime-to-q marking.
      D.CentralIsMultiplicationByQ hcorrespondences hgood.2.2.1 ∧
      D.IsCentralGraph markingShift ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        D.neighbors (AbelianScheme.TateComparison.Local.IntegralType.central s) b x = {x ≫ markingShift.hom}) ∧

      -- Central shifts clear arbitrary chosen and opposite exponents.
      (∀ t : AbelianScheme.TateComparison.Local.LocalType s, ∃ (n : ℕ) (u : AbelianScheme.TateComparison.Local.IntegralType s),
        basis (AbelianScheme.TateComparison.Local.LocalType.central s) ^ n * basis t = basis u.val) ∧

      ∃ (TAlb : AbelianScheme.TateComparison.Local.IntegralType s → D.EndK)
        (ρ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
        (ρH1 : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1),

        (∀ t : AbelianScheme.TateComparison.Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧

        -- Actual homomorphisms over K act by point push on component differences.
        (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
            (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
            (x y : Over.mk b ⟶ D.componentGeneric j),
          D.endPoint (TAlb t) (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
            ((D.neighbors t b (x ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum -
            ((D.neighbors t b (y ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum) ∧

        (∀ u v : AbelianScheme.TateComparison.Local.IntegralType s,
          TAlb u * TAlb v = (coeff u v).sum (fun w n => n • TAlb w)) ∧
        IsUnit (ρ (basis (AbelianScheme.TateComparison.Local.LocalType.central s))) ∧

        -- Pullback on actual rational Betti H1, including rational endomorphisms.
        (∀ h : AbelianScheme.TateComparison.HeckeKernel.Hecke s q, D.IsRationalH1Pullback (ρ h) (ρH1 h)) ∧

        -- Pullback on one-forms equals the actual sum over target branches.
        (∀ (t : AbelianScheme.TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
          AbelianScheme.TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t)
            (D.albanesePullback hgeometry ω)
            (D.albanesePullback hgeometry (D.pullbackForms (TAlb t) ω)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison.CM
