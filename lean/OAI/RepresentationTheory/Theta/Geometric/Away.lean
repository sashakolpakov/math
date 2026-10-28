import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Away -/

namespace OAI.RepresentationTheory.Theta.Geometric.Away.Spherical

noncomputable section

/-! The local spherical action preserves the prescribed away-level fixed
condition, because the two factors of the finite group commute. -/

variable {G A S : Type*} [Group G] [Group A]
  [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
  (K : Subgroup G) (L : Subgroup A) (rho : G × A →* (S ≃ₗ[ℂ] S))

omit [Module ℚ S] [IsScalarTower ℚ ℂ S] in
theorem fixedProduct_iff (v : S) :
    v ∈ SphericalGU.Spherical.fixedInputs (K.prod L) rho ↔
      v ∈ SphericalGU.Spherical.fixedInputs K (rho.comp (MonoidHom.inl G A)) ∧
      v ∈ SphericalGU.Spherical.fixedInputs L (rho.comp (MonoidHom.inr G A)) := by
  constructor
  · intro hv
    exact ⟨fun k hk => hv (k, 1) ⟨hk, L.one_mem⟩,
      fun a ha => hv (1, a) ⟨K.one_mem, ha⟩⟩
  · rintro ⟨hk, ha⟩ ⟨k, a⟩ ⟨hkm, ham⟩
    change rho (k, a) v = v
    have he : (k, a) = (k, 1) * (1, a) := by simp
    have hka : rho (k, 1) v = v := hk k hkm
    have haa : rho (1, a) v = v := ha a ham
    rw [he, map_mul, LinearEquiv.mul_apply, haa, hka]

theorem local_weil_preserves_product
    (T : SphericalGU.Spherical.algebra K) (φ : SphericalGU.Spherical.fixedInputs (K.prod L) rho) :
    SphericalGU.Spherical.weilOperator K (rho.comp (MonoidHom.inl G A)) T φ.val ∈
      SphericalGU.Spherical.fixedInputs (K.prod L) rho := by
  obtain ⟨hk, ha⟩ := (fixedProduct_iff K L rho φ.val).mp φ.property
  apply (fixedProduct_iff K L rho _).mpr
  refine ⟨SphericalGU.Spherical.weilOperator_preserves_fixed K (rho.comp (MonoidHom.inl G A)) T ⟨φ.val, hk⟩, ?_⟩
  intro a ham
  have haa : rho (1, a) φ.val = φ.val := ha a ham
  have hcomm (g : G) : rho (1, a) (rho (g, 1) φ.val) = rho (g, 1) φ.val := by
    have he : (1, a) * (g, 1) = (g, 1) * (1, a) := by simp
    rw [← LinearEquiv.mul_apply, ← map_mul, he, map_mul, LinearEquiv.mul_apply,
      haa]
  change rho (1, a) (SphericalGU.Spherical.weilOperator K (rho.comp (MonoidHom.inl G A)) T φ.val) = _
  unfold SphericalGU.Spherical.weilOperator
  rw [LinearMap.finsupp_sum_apply]
  simp only [Finsupp.sum, LinearMap.smul_apply, LinearEquiv.coe_coe,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, map_sum, map_smul, hcomm]

def productWeilAction (T : SphericalGU.Spherical.algebra K) :
    SphericalGU.Spherical.fixedInputs (K.prod L) rho →ₗ[ℂ] SphericalGU.Spherical.fixedInputs (K.prod L) rho :=
  LinearMap.codRestrict _
    ((SphericalGU.Spherical.weilOperator K (rho.comp (MonoidHom.inl G A)) T).comp
      (SphericalGU.Spherical.fixedInputs (K.prod L) rho).subtype)
    (local_weil_preserves_product K L rho T)

theorem productWeilAction_val (T : SphericalGU.Spherical.algebra K) (φ : SphericalGU.Spherical.fixedInputs (K.prod L) rho) :
    (productWeilAction K L rho T φ).val =
      SphericalGU.Spherical.evaluateKernel K (rho.comp (MonoidHom.inl G A))
        ⟨φ.val, ((fixedProduct_iff K L rho φ.val).mp φ.property).1⟩ (SphericalGU.Spherical.kernel K T) := by
  change SphericalGU.Spherical.weilOperator K (rho.comp (MonoidHom.inl G A)) T φ.val = _
  exact SphericalGU.Spherical.weilOperator_eq_evaluateKernel K (rho.comp (MonoidHom.inl G A)) T
    ⟨φ.val, ((fixedProduct_iff K L rho φ.val).mp φ.property).1⟩

/-- The spherical Weil action is rational-linear in its actual Hecke
kernel, so complex coefficients are obtained by genuine scalar extension. -/
def productWeilActionLinear : SphericalGU.Spherical.algebra K →ₗ[ℚ]
    Module.End ℂ (SphericalGU.Spherical.fixedInputs (K.prod L) rho) where
  toFun := productWeilAction K L rho
  map_add' T U := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change (productWeilAction K L rho (T + U) φ).val =
      (productWeilAction K L rho T φ).val + (productWeilAction K L rho U φ).val
    have hk : SphericalGU.Spherical.kernel K (T + U) = SphericalGU.Spherical.kernel K T + SphericalGU.Spherical.kernel K U := rfl
    simp only [productWeilAction_val, hk, map_add]
  map_smul' r T := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change (productWeilAction K L rho (r • T) φ).val =
      r • (productWeilAction K L rho T φ).val
    have hk : SphericalGU.Spherical.kernel K (r • T) = r • SphericalGU.Spherical.kernel K T := rfl
    simp only [productWeilAction_val, hk, map_smul]

end

end OAI.RepresentationTheory.Theta.Geometric.Away.Spherical
