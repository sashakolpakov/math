import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonBetti
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonProjectors

/-! # Summand Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SummandTransport

noncomputable section

/-! Actual intertwining, rather than an equality of independently chosen
summands, transports simultaneous generalized eigenspaces. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

namespace Comparison

theorem intertwining_genEigenspace_iff
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (T : Module.End K V) (U : Module.End K W)
    (h : ∀ x, e (T x) = U (e x)) (μ : K) (x : V) :
    x ∈ T.genEigenspace μ ⊤ ↔ e x ∈ U.genEigenspace μ ⊤ := by
  have hp : ∀ (n : ℕ) (x : V), e (((T - μ • 1) ^ n) x) =
      ((U - μ • 1) ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp only [pow_zero, Module.End.one_apply]
    | succ n ih =>
      intro x
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, h, ih]
  simp only [Module.End.mem_genEigenspace_top, LinearMap.mem_ker]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hp n x).symm.trans (by rw [hn, map_zero])⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective ((hp n x).trans (hn.trans (map_zero e).symm))⟩

theorem jointSpace_map_equiv
    {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (T : I → Module.End K V) (U : I → Module.End K W)
    (h : ∀ i x, e (T i x) = U i (e x)) (χ : I → K) :
    (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace T χ).map e.toLinearMap = NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand U χ := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv]
  simp only [HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace, NumberTheory.PadicHodge.GeometricComparison.Linear.generalizedHeckeSummand,
    Module.End.maxGenEigenspace, Submodule.mem_iInf, LinearEquiv.symm_apply_apply]
  exact forall_congr' (fun i => intertwining_genEigenspace_iff e (T i) (U i) (h i) (χ i) x)

theorem conjugate_range
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (P : Module.End K V) :
    LinearMap.range (e.conj P) = (LinearMap.range P).map e.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, congrArg (fun x => e (P x)) (e.symm_apply_apply z)⟩

end Comparison

namespace Intrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_comparison_summand
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
    ∀ (R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R =
        (fun h => (Intrinsic.Forms.activeBettiAction D A e h : Module.End ℚ D.pel.H1)) →
      ∀ χ : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q → ℂ,
        (HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (Intrinsic.Forms.activeBettiAction D A e h).baseChange ℂ) χ).map
          (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap =
        (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHeckeSummand D.pel.complexEmbedding R χ := by
  let := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
  intro R hR χ
  exact Comparison.jointSpace_map_equiv (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg)
    _ _ (ComparisonBetti.Intrinsic.native_comparison_intertwining D hg hq A e hElementaryDivisors j R hR) χ

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SummandTransport
