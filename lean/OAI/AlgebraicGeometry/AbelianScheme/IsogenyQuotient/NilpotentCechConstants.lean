import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorNilpotentDevissage
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatKernelProd
import Mathlib.RingTheory.Flat.Stability

/-! # Nilpotent Cech Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechConstants.Construction

noncomputable section

/-! A split augmented complex over a nilpotent thickening of a field
has only constant degree-zero cycles when this is true on its residue
field and its degree-one module is flat. No finite-generation premise
on its degree-zero module is needed. -/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

theorem injective_of_nilpotent_residue_injective [Module.Flat R N]
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I) (b : M →ₗ[R] N)
    (hb : Function.Injective (b.lTensor (R ⧸ I))) : Function.Injective b := by
  obtain ⟨n, hn⟩ := hI
  have hR : Function.Injective (b.lTensor R) :=
    HilbertScheme.Presentations.TensorNilpotentDevissage.lTensor_injective_of_maximalIdeal_power b I hb n R
      (by rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul])
  intro x y hxy
  have h := hR (show b.lTensor R (1 ⊗ₜ[R] x) = b.lTensor R (1 ⊗ₜ[R] y) by
    simp only [LinearMap.lTensor_tmul, hxy])
  simpa only [TensorProduct.lid_tmul, one_smul] using congrArg (TensorProduct.lid R M) h

theorem split_augmentation_residue_detector_injective
    (I : Ideal R) (a : R →ₗ[R] M) (e : M →ₗ[R] R) (d : M →ₗ[R] N)
    (hea : e.comp a = LinearMap.id)
    (hres : Function.Exact (a.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I))) :
    Function.Injective ((e.prod d).lTensor (R ⧸ I)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have he : e.lTensor (R ⧸ I) x = 0 := by
    have h := congrArg ((LinearMap.fst R R N).lTensor (R ⧸ I)) hx
    have hp : (LinearMap.fst R R N).comp (e.prod d) = e := by ext z; rfl
    simpa only [← LinearMap.lTensor_comp_apply, hp, map_zero] using h
  have hd : d.lTensor (R ⧸ I) x = 0 := by
    have h := congrArg ((LinearMap.snd R R N).lTensor (R ⧸ I)) hx
    have hp : (LinearMap.snd R R N).comp (e.prod d) = d := by ext z; rfl
    simpa only [← LinearMap.lTensor_comp_apply, hp, map_zero] using h
  obtain ⟨r, hr⟩ := (hres x).mp hd
  have hr0 : r = 0 := by
    have h := he
    rw [← hr, ← LinearMap.lTensor_comp_apply, hea, LinearMap.lTensor_id, LinearMap.id_apply] at h
    exact h
  rw [← hr, hr0, map_zero]

theorem nilpotent_split_augmentation_constants [Module.Flat R N]
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I)
    (a : R →ₗ[R] M) (e : M →ₗ[R] R) (d : M →ₗ[R] N)
    (hea : e.comp a = LinearMap.id) (hda : d.comp a = 0)
    (hres : Function.Exact (a.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I)))
    (x : M) (hx : d x = 0) : x = a (e x) := by
  have : Module.Flat R (R × N) := Quotients.FiniteDescent.FlatKernelProd.Construction.FlatKernel.prod
  apply injective_of_nilpotent_residue_injective I hI (e.prod d)
    (split_augmentation_residue_detector_injective I a e d hea hres)
  apply Prod.ext
  · exact (LinearMap.congr_fun hea (e x)).symm
  · exact hx.trans (LinearMap.congr_fun hda (e x)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechConstants.Construction
