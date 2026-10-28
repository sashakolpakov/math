import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates

/-! # Type Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport

noncomputable section

/-! CM types and their actual Hodge realizations transport along field
isomorphisms. This permits applying the exact embedded-field RiemannProjectivity input
to an abstract coefficient number field. -/

open scoped Classical TensorProduct

def hodgeRealizationAlongEquiv
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    (e : U ≃ₗ[ℚ] V) (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J e.toLinearMap)
    (hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap J H e.symm.toLinearMap) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization H where
  abelianVariety := R.abelianVariety
  comparison := e.trans R.comparison
  holomorphic x := by
    rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp, LinearMap.comp_apply,
      R.holomorphic]
    constructor
    · intro hx
      have h := hi _ hx
      change (e.baseChange ℚ ℂ _ _).symm ((e.baseChange ℚ ℂ _ _) x) ∈ H.holomorphic at h
      rwa [LinearEquiv.symm_apply_apply] at h
    · exact he x
  antiholomorphic x := by
    rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp, LinearMap.comp_apply,
      R.antiholomorphic]
    constructor
    · intro hx
      have h := hi.map_antiholomorphic hx
      change (e.baseChange ℚ ℂ _ _).symm ((e.baseChange ℚ ℂ _ _) x) ∈ H.antiholomorphic at h
      rwa [LinearEquiv.symm_apply_apply] at h
    · exact he.map_antiholomorphic

variable {E F : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field F] [NumberField F] [Algebra ℚ F] [NumberField.IsCMField F]

def cmTypeAlongEquiv (e : E ≃ₐ[ℚ] F) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType F :=
  ⟨fun σ => ε.val (σ.comp e.toAlgHom), fun σ => by
    exact ε.property (σ.comp e.toAlgHom)⟩

omit [NumberField.IsCMField E] [NumberField.IsCMField F] in
theorem fieldComplexificationEquiv_map (e : E ≃ₐ[ℚ] F)
    (x : ComplexMultiplication.WeightOne.CM.Complexification E) (σ : F →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv F (e.toLinearMap.baseChange ℂ x) σ =
      ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (σ.comp e.toAlgHom) := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

omit [NumberField.IsCMField E] [NumberField.IsCMField F] in
theorem cmTypeAlongEquiv_subspace (e : E ≃ₐ[ℚ] F) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (t : Bool) (x : ComplexMultiplication.WeightOne.CM.Complexification E) :
    e.toLinearMap.baseChange ℂ x ∈ (cmTypeAlongEquiv e ε).subspace t ↔ x ∈ ε.subspace t := by
  rw [ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mem_subspace_iff, ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.mem_subspace_iff]
  constructor
  · intro hx σ hσ
    have hcomp : (σ.comp e.symm.toAlgHom).comp e.toAlgHom = σ := by ext a; simp
    have h := hx (σ.comp e.symm.toAlgHom)
    rw [fieldComplexificationEquiv_map, hcomp] at h
    change ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ ≠ 0 →
      ε.val ((σ.comp e.symm.toAlgHom).comp e.toAlgHom) = t at h
    rw [hcomp] at h
    exact h hσ
  · intro hx σ hσ
    rw [fieldComplexificationEquiv_map] at hσ
    exact hx (σ.comp e.toAlgHom) hσ

omit [NumberField.IsCMField E] [NumberField.IsCMField F] in
theorem cmTypeAlongEquiv_hodgeMap (e : E ≃ₐ[ℚ] F) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap ε.hodgeStructure (cmTypeAlongEquiv e ε).hodgeStructure e.toLinearMap :=
  fun x hx => (cmTypeAlongEquiv_subspace e ε true x).mpr hx

omit [NumberField.IsCMField E] [NumberField.IsCMField F] in
theorem cmTypeAlongEquiv_inverse_hodgeMap (e : E ≃ₐ[ℚ] F) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (cmTypeAlongEquiv e ε).hodgeStructure ε.hodgeStructure e.symm.toLinearMap := by
  intro x hx
  apply (cmTypeAlongEquiv_subspace e ε true _).mp
  change (e.toLinearEquiv.baseChange ℚ ℂ _ _)
    ((e.toLinearEquiv.baseChange ℚ ℂ _ _).symm x) ∈ _
  rw [LinearEquiv.apply_symm_apply]
  exact hx

def cmRealizationAlongEquiv (e : E ≃ₐ[ℚ] F) (ε : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (cmTypeAlongEquiv e ε).hodgeStructure) :
    ComplexMultiplication.CMKnownResults.CM.HodgeRealization ε.hodgeStructure :=
  hodgeRealizationAlongEquiv e.toLinearEquiv (cmTypeAlongEquiv_hodgeMap e ε)
    (cmTypeAlongEquiv_inverse_hodgeMap e ε) R

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport
