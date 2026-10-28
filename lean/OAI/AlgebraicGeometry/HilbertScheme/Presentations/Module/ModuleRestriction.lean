import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions

/-! # Module Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ModuleRestriction.GradedModules

noncomputable section

/-! Actual module restriction maps when a principal denominator divides another. -/

universe u v

variable {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

theorem awayModuleFactor_isUnit (a b c : A) (h : b = a * c) :
    IsUnit (algebraMap A (Module.End A (Fractions.GradedModules.AwayModule b M)) a) := by
  have hb := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers b) M)
    (Fractions.GradedModules.moduleDenominator b 1)
  let φ := algebraMap A (Module.End A (Fractions.GradedModules.AwayModule b M))
  change IsUnit (φ (b ^ 1)) at hb
  have he : φ b = φ a * φ c := (congrArg φ h).trans (map_mul φ a c)
  rw [pow_one, he, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at hb
  exact hb.1

def awayModuleRestriction (a b c : A) (h : b = a * c) : Fractions.GradedModules.AwayModule a M →ₗ[A] Fractions.GradedModules.AwayModule b M :=
  LocalizedModule.lift (Submonoid.powers a) (LocalizedModule.mkLinearMap (Submonoid.powers b) M)
    (fun s => by
      obtain ⟨k, hk⟩ := s.property
      change IsUnit (algebraMap A (Module.End A (Fractions.GradedModules.AwayModule b M)) s.val)
      rw [← hk, map_pow]
      exact (awayModuleFactor_isUnit M a b c h).pow k)

theorem awayModuleRestriction_mk_one (a b c : A) (h : b = a * c) (m : M) :
    awayModuleRestriction M a b c h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one _ _ _ m

theorem awayModuleRestriction_comp_mk (a b c : A) (h : b = a * c) :
    (awayModuleRestriction M a b c h).comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M) =
      LocalizedModule.mkLinearMap (Submonoid.powers b) M :=
  LocalizedModule.lift_comp _ _ _

theorem awayModuleRestriction_unique (a b c : A) (h : b = a * c)
    (f : Fractions.GradedModules.AwayModule a M →ₗ[A] Fractions.GradedModules.AwayModule b M)
    (hf : f.comp (LocalizedModule.mkLinearMap (Submonoid.powers a) M) =
      LocalizedModule.mkLinearMap (Submonoid.powers b) M) :
    awayModuleRestriction M a b c h = f :=
  LocalizedModule.lift_unique _ _ _ f hf

theorem awayModuleRestriction_refl (a : A) :
    awayModuleRestriction M a a 1 (mul_one a).symm = LinearMap.id := by
  apply awayModuleRestriction_unique
  rfl

theorem awayModuleRestriction_comp (a b c b' c' : A) (h : b = a * c) (h' : b' = b * c') :
    (awayModuleRestriction M b b' c' h').comp (awayModuleRestriction M a b c h) =
      awayModuleRestriction M a b' (c * c') (by rw [h', h, mul_assoc]) := by
  symm
  apply awayModuleRestriction_unique
  rw [LinearMap.comp_assoc, awayModuleRestriction_comp_mk, awayModuleRestriction_comp_mk]

theorem awayModuleRestriction_fraction (a b c : A) (h : b = a * c) (k : ℕ) (m : M) :
    awayModuleRestriction M a b c h (LocalizedModule.mk m (Fractions.GradedModules.moduleDenominator a k)) =
      LocalizedModule.mk (c ^ k • m) (Fractions.GradedModules.moduleDenominator b k) := by
  have hu := (awayModuleFactor_isUnit M a b c h).pow k
  rw [← map_pow] at hu
  apply ((Module.End.isUnit_iff _).mp hu).injective
  change a ^ k • awayModuleRestriction M a b c h (LocalizedModule.mk m (Fractions.GradedModules.moduleDenominator a k)) =
    a ^ k • LocalizedModule.mk (c ^ k • m) (Fractions.GradedModules.moduleDenominator b k)
  rw [← map_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, ← mul_smul,
    ← mul_pow, ← h]
  have hs : LocalizedModule.mk (a ^ k • m) (Fractions.GradedModules.moduleDenominator a k) =
      LocalizedModule.mk m (1 : Submonoid.powers a) :=
    LocalizedModule.mk_cancel (Fractions.GradedModules.moduleDenominator a k) m
  have ht : LocalizedModule.mk (b ^ k • m) (Fractions.GradedModules.moduleDenominator b k) =
      LocalizedModule.mk m (1 : Submonoid.powers b) :=
    LocalizedModule.mk_cancel (Fractions.GradedModules.moduleDenominator b k) m
  rw [hs, ht, awayModuleRestriction_mk_one]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ModuleRestriction.GradedModules
