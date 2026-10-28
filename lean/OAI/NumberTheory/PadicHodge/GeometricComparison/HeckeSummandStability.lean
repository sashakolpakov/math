import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Hecke Summand Stability -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandStability.GeneralizedHecke

noncomputable section

/-! A commuting invertible operator restricts to every simultaneous generalized Hecke eigenspace. -/

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem commutes_inverse (φ : V ≃ₗ[K] V) (T : Module.End K V)
    (h : Commute T φ.toLinearMap) : Commute T φ.symm.toLinearMap := by
  change T.comp φ.symm.toLinearMap = φ.symm.toLinearMap.comp T
  apply LinearMap.ext
  intro x
  apply φ.injective
  have hx := LinearMap.congr_fun h.eq (φ.symm x)
  change T (φ (φ.symm x)) = φ (T (φ.symm x)) at hx
  change φ (T (φ.symm x)) = φ (φ.symm (T x))
  simpa only [φ.apply_symm_apply] using hx.symm

theorem summand_stable (φ : V ≃ₗ[K] V) (T : I → Module.End K V) (χ : I → K)
    (h : ∀ i, Commute (T i) φ.toLinearMap) :
    Linear.generalizedHeckeSummand T χ ≤ (Linear.generalizedHeckeSummand T χ).comap φ.toLinearMap := by
  intro x hx
  apply (Linear.mem_generalizedHeckeSummand T χ (φ x)).mpr
  intro i
  exact (Module.End.mapsTo_maxGenEigenspace_of_comm (h i) (χ i))
    ((Linear.mem_generalizedHeckeSummand T χ x).mp hx i)

def restriction (φ : V ≃ₗ[K] V) (T : I → Module.End K V) (χ : I → K)
    (h : ∀ i, Commute (T i) φ.toLinearMap) :
    Linear.generalizedHeckeSummand T χ ≃ₗ[K] Linear.generalizedHeckeSummand T χ where
  toFun x := ⟨φ x, summand_stable φ T χ h x.property⟩
  invFun x := ⟨φ.symm x, summand_stable φ.symm T χ (fun i => commutes_inverse φ (T i) (h i)) x.property⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : V))
  right_inv x := Subtype.ext (φ.apply_symm_apply (x : V))
  map_add' x y := Subtype.ext (φ.map_add (x : V) (y : V))
  map_smul' a x := Subtype.ext (φ.map_smul a (x : V))

theorem restriction_apply (φ : V ≃ₗ[K] V) (T : I → Module.End K V) (χ : I → K)
    (h : ∀ i, Commute (T i) φ.toLinearMap) (x : Linear.generalizedHeckeSummand T χ) :
    (restriction φ T χ h x : V) = φ (x : V) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandStability.GeneralizedHecke
