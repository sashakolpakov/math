import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.PrincipalCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.QuotientCoordinates

/-! # Quotient Matrices -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.QuotientMatrices.Grassmannian

noncomputable section

/-! Actual quotient submodules have normalized matrices on principal neighborhoods. -/

open _root_.Module LocalizedModule

universe u

variable {R M ι ν : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

def selectedLocalizedBasis (v : ν → M) (a : ι → ν) (r : R)
    (h : Function.Bijective (LocalizedModule.map (Submonoid.powers r)
      (Fintype.linearCombination R (v ∘ a)))) :
    Basis ι (Localization.Away r) (LocalizedModule.Away r M) :=
  ((Pi.basisFun R ι).ofIsLocalizedModule (Localization.Away r) (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) (ι → R))).map (LinearEquiv.ofBijective _ h)

omit [Fintype ν] [DecidableEq ν] in
theorem selectedLocalizedBasis_apply (v : ν → M) (a : ι → ν) (r : R)
    (h : Function.Bijective (LocalizedModule.map (Submonoid.powers r)
      (Fintype.linearCombination R (v ∘ a)))) (i : ι) :
    selectedLocalizedBasis v a r h i = LocalizedModule.mkLinearMap (Submonoid.powers r) M (v (a i)) := by
  simp only [selectedLocalizedBasis, Basis.map_apply, Basis.ofIsLocalizedModule_apply,
    Pi.basisFun_apply, LinearEquiv.ofBijective_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.map_mk, Fintype.linearCombination_apply_single, one_smul, Function.comp_apply]

theorem quotient_principal_normalized_matrix
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) (p : PrimeSpectrum R) :
    ∃ (r : R) (a : ι → ν) (Q : Matrix ι ν (Localization.Away r)),
      r ∉ p.asIdeal ∧ Function.Injective a ∧ Normalized.Matrices.Grassmannian.IsNormalized a Q ∧
      (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R (Localization.Away r)) N.toSubmodule := by
  let v : ν → (ν → R) ⧸ N.toSubmodule := fun j => N.toSubmodule.mkQ (Pi.single j 1)
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    have he : v = N.toSubmodule.mkQ ∘ Pi.basisFun R ν := by
      funext j
      simp only [v, Function.comp_apply, Pi.basisFun_apply]
    rw [he]
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun R ν).span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective
  obtain ⟨r, a, hr, ha, hbij⟩ := Quotient.PrincipalCharts.Grassmannian.generators_principal_basis v hv N.rankAtStalk_eq p
  let B := selectedLocalizedBasis v a r hbij
  refine ⟨r, a, Localized.QuotientCoordinates.Grassmannian.localizedBasisMatrix (Submonoid.powers r) N.toSubmodule.mkQ B, hr, ha, ?_, ?_⟩
  · apply Localized.QuotientCoordinates.Grassmannian.localizedBasisMatrix_normalized
    exact selectedLocalizedBasis_apply v a r hbij
  · rw [Localized.QuotientCoordinates.Grassmannian.localizedBasisMatrix_kernel, N.toSubmodule.ker_mkQ]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.QuotientMatrices.Grassmannian
