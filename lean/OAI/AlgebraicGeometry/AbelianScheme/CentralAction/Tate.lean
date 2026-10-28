import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface

/-! # Tate -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Tate.Construction

noncomputable section

/-! The unbundled TateComparison conclusion is transcribed from its committed
specification. The equivalence below checks that Conclusion adds no
hypothesis and loses none of the supplied conclusion clauses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def SpecificationConclusion (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient) : Prop :=
    -- All geometric flags have ordinary chosen-block lattice realizations;
    -- opposite lattices, composite polarizations, and markings agree.
    D.HasPolarizedFlagRealizations hcorrespondences ∧

    ∃ (basis : TateComparison.Local.LocalType s → TateComparison.HeckeKernel.Hecke s q)
      (coeff : TateComparison.Local.IntegralType s → TateComparison.Local.IntegralType s → TateComparison.Local.IntegralType s →₀ ℕ)
      (markingShift : D.space ≅ D.space),

      -- The basis and its coefficients have their actual raw convolution meaning.
      (∀ t, TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) (basis t)) ∧
      (∀ u v : TateComparison.Local.IntegralType s,
        basis u.val * basis v.val =
          (coeff u v).sum (fun w n => n • basis w.val)) ∧
      (∀ (u v : TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        (D.neighbors u b x).bind (D.neighbors v b) =
          (coeff u v).sum (fun w n => n • D.neighbors w b x)) ∧

      -- The central isogeny is [q] with the transported prime-to-q marking.
      D.CentralIsMultiplicationByQ hcorrespondences hgood.2.2.1 ∧
      D.IsCentralGraph markingShift ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k]
          (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b),
        D.neighbors (TateComparison.Local.IntegralType.central s) b x = {x ≫ markingShift.hom}) ∧

      -- Central shifts clear arbitrary chosen and opposite exponents.
      (∀ t : TateComparison.Local.LocalType s, ∃ (n : ℕ) (u : TateComparison.Local.IntegralType s),
        basis (TateComparison.Local.LocalType.central s) ^ n * basis t = basis u.val) ∧

      ∃ (TAlb : TateComparison.Local.IntegralType s → D.EndK)
        (ρ : TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
        (ρH1 : TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1),

        (∀ t : TateComparison.Local.IntegralType s, D.toRational (TAlb t) = ρ (basis t.val)) ∧

        -- Actual homomorphisms over K act by point push on component differences.
        (∀ (t : TateComparison.Local.IntegralType s) (k : Type) [Field k] [IsAlgClosed k]
            (b : Spec (.of k) ⟶ Spec (.of K)) (j : Fin D.componentCount)
            (x y : Over.mk b ⟶ D.componentGeneric j),
          D.endPoint (TAlb t) (D.aPoint hgeometry j x - D.aPoint hgeometry j y) =
            ((D.neighbors t b (x ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum -
            ((D.neighbors t b (y ≫ D.componentInclusion j)).map
              (D.aTotalPoint hgeometry)).sum) ∧

        (∀ u v : TateComparison.Local.IntegralType s,
          TAlb u * TAlb v = (coeff u v).sum (fun w n => n • TAlb w)) ∧
        IsUnit (ρ (basis (TateComparison.Local.LocalType.central s))) ∧

        -- Pullback on actual rational Betti H1, including rational endomorphisms.
        (∀ h : TateComparison.HeckeKernel.Hecke s q, D.IsRationalH1Pullback (ρ h) (ρH1 h)) ∧

        -- Pullback on one-forms equals the actual sum over target branches.
        (∀ (t : TateComparison.Local.IntegralType s) (ω : D.OneFormsA),
          TateComparison.Branches.IsBranchTrace (D.complexCorrespondence t)
            (D.albanesePullback hgeometry ω)
            (D.albanesePullback hgeometry (D.pullbackForms (TAlb t) ω)))

/-- The action record is equivalent to the exact unbundled TateComparison conclusion. -/
theorem c47_input_equivalence (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime)
    (hcorrespondences : D.RealizesIsogenyQuotient) :
    SpecificationConclusion D hgeometry hgood hcorrespondences ↔
      ∃ A : Interface.Construction.ActionData D, Interface.Construction.Conclusion D hgeometry hgood hcorrespondences A := by
  constructor
  · rintro ⟨hflags, basis, coeff, shift, hraw, hcoeff, hneighbors, hscalar,
      hgraph, hscalarNeighbors, hclears, TAlb, rho, rhoH1, hintegral,
      hpointPush, hmul, hunit, hcohomology, hforms⟩
    exact ⟨⟨basis, coeff, shift, TAlb, rho, rhoH1⟩,
      ⟨hflags, hraw, hcoeff, hneighbors, hscalar, hgraph, hscalarNeighbors,
        hclears, hintegral, hpointPush, hmul, hunit, hcohomology, hforms⟩⟩
  · rintro ⟨A, h⟩
    exact ⟨h.flags, A.basis, A.coeff, A.markingShift, h.raw, h.coefficients,
      h.neighbors, h.scalarIsogeny, h.scalarGraph, h.scalarNeighbors, h.clears,
      A.TAlb, A.rho, A.rhoH1, h.integral, h.pointPush,
      h.integralMultiplication, h.scalarUnit, h.cohomology, h.forms⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Tate.Construction
