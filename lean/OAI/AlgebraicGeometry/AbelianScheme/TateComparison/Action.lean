import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConcreteRationalHeckeAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeForms
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedFlagRealizations
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralUniversalMultiplication

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action

noncomputable section

/-! Full construction of the spherical Hecke action with the original
geometric, integral, rational, Betti, and affine branch-trace clauses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem spherical_hecke_algebra_action_constructed
    {E K : Type}
    [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K]
    (s : ℕ) (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (q : ℕ) [Fact q.Prime]
    (D : Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient)
    (_hE07 : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    -- All geometric flags have ordinary chosen-block lattice realizations;
    -- opposite lattices, composite polarizations, and markings agree.
    D.HasPolarizedFlagRealizations hcorrespondences ∧

    ∃ (basis : Local.LocalType s → HeckeKernel.Hecke s q)
      (coeff : Local.IntegralType s → Local.IntegralType s → Local.IntegralType s →₀ ℕ)
      (markingShift : D.space ≅ D.space),

      -- The basis and its coefficients have their actual raw convolution meaning.
      (∀ t, HeckeKernel.IsRawDoubleCoset (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t) (basis t)) ∧
      (∀ u v : Local.IntegralType s,
        basis u.val * basis v.val =
          (coeff u v).sum (fun w n => n • basis w.val)) ∧
      (∀ (u v : Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        (D.neighbors u b x).bind (D.neighbors v b) =
          (coeff u v).sum (fun w n => n • D.neighbors w b x)) ∧

      -- The central isogeny is [q] with the transported prime-to-q marking.
      D.CentralIsMultiplicationByQ hcorrespondences hgood.2.2.1 ∧
      D.IsCentralGraph markingShift ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        D.neighbors (Local.IntegralType.central s) b x = {x ≫ markingShift.hom}) ∧

      -- Central shifts clear arbitrary chosen and opposite exponents.
      (∀ t : Local.LocalType s, ∃ (n : ℕ) (u : Local.IntegralType s),
        basis (Local.LocalType.central s) ^ n * basis t = basis u.val) ∧

      ∃ (TAlb : Local.IntegralType s → D.EndK)
        (ρ : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
        (ρH1 : HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1),

        (∀ t : Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧

        -- Actual homomorphisms over K act by point push on component differences.
        (∀ (t : Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
            (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
            (x y : Over.mk b ⟶ D.componentGeneric j),
          D.endPoint (TAlb t) (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
            ((D.neighbors t b (x ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum -
            ((D.neighbors t b (y ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum) ∧

        (∀ u v : Local.IntegralType s,
          TAlb u * TAlb v = (coeff u v).sum (fun w n => n • TAlb w)) ∧
        IsUnit (ρ (basis (Local.LocalType.central s))) ∧

        -- Pullback on actual rational Betti H1, including rational endomorphisms.
        (∀ h : HeckeKernel.Hecke s q, D.IsRationalH1Pullback (ρ h) (ρH1 h)) ∧

        -- Pullback on one-forms equals the actual sum over target branches.
        (∀ (t : Local.IntegralType s) (ω : D.OneFormsA),
          Branches.IsBranchTrace (D.complexCorrespondence t)
            (D.albanesePullback hgeometry ω)
            (D.albanesePullback hgeometry (D.pullbackForms (TAlb t) ω))) := by
  refine ⟨D.hasPolarizedFlagRealizations hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    CentralConvolution.sphericalBasis s q, ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors,
    D.qMarkingAutomorphism hgeometry hgood.2.2.1,
    CentralConvolution.sphericalBasis_isRaw s q,
    ConvolutionCoefficients.spherical_convolution s q hElementaryDivisors, ?_,
    D.centralIsMultiplicationByQ hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    D.isCentralGraph_qMarking hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors, ?_,
    CentralConvolution.sphericalBasis_exists_integral_shift s q,
    D.heckeEnd hgeometry,
    D.rationalHeckeAction hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    D.actualSphericalH1Action hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    ?_, ?_,
    D.heckeEnd_convolution hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    D.rationalHeckeAction_central_isUnit hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    D.actualSphericalH1Action_spec hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors,
    D.heckeEnd_branchTrace hgeometry⟩
  · intro u v k _ _ b x
    exact D.neighbors_convolution hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors u v b x
  · intro k _ _ b x
    exact D.central_neighbors_marking hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors b x
  · intro t
    exact (D.rationalHeckeAction_basis hgood hdegree hs hgeometry hcorrespondences hElementaryDivisors t).symm
  · intro t k _ _ b j x y
    exact D.heckeEnd_point_push hgeometry t b j x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action
