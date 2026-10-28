import Mathlib.RingTheory.Localization.Module

/-! # Localized Module Scalars -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedModuleScalars.BundleCycles

noncomputable section

/-! # LineBundleCycles: localization under restriction of the scalar ring -/

variable {R A M N : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]

theorem isLocalizedModule_of_restrictScalars (D : Submonoid R) (f : M →ₗ[A] N)
    [IsLocalizedModule D (f.restrictScalars R)] :
    IsLocalizedModule (D.map (algebraMap R A)) f where
  map_units d := by
    obtain ⟨r, hr, he⟩ := d.property
    have h := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (f.restrictScalars R) (⟨r, hr⟩ : D))
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun n : N => d.val • n)
    change Function.Bijective (fun n : N => r • n) at h
    rw [← he]
    simpa only [algebraMap_smul] using h
  surj n := by
    obtain ⟨⟨m, d⟩, hd⟩ := IsLocalizedModule.surj D (f.restrictScalars R) n
    refine ⟨⟨m, ⟨algebraMap R A d.val, Submonoid.mem_map_of_mem _ d.property⟩⟩, ?_⟩
    change algebraMap R A d.val • n = f m
    rw [algebraMap_smul]
    exact hd
  exists_of_eq h := by
    obtain ⟨d, hd⟩ := IsLocalizedModule.exists_of_eq (S := D) (f := f.restrictScalars R) h
    refine ⟨⟨algebraMap R A d.val, Submonoid.mem_map_of_mem _ d.property⟩, ?_⟩
    simpa only [Submonoid.smul_def, algebraMap_smul] using hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedModuleScalars.BundleCycles
