import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Linear Extension -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.LinearExtension

noncomputable section

/-! # Extending linear maps into complete modules, with exact naturality -/

variable {R M N P Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  (I : Ideal R) [IsAdicComplete I N]

def extension (f : M →ₗ[R] N) : AdicCompletion I M →ₗ[R] N :=
  (AdicCompletion.ofLinearEquiv I N).symm.toLinearMap.comp ((AdicCompletion.map I f).restrictScalars R)

theorem extension_of (f : M →ₗ[R] N) (x : M) : extension I f (AdicCompletion.of I M x) = f x := by
  change (AdicCompletion.ofLinearEquiv I N).symm (AdicCompletion.map I f (AdicCompletion.of I M x)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]

theorem of_extension (f : M →ₗ[R] N) (x : AdicCompletion I M) :
    AdicCompletion.of I N (extension I f x) = AdicCompletion.map I f x :=
  AdicCompletion.of_ofLinearEquiv_symm I _

theorem extension_map (f : Q →ₗ[R] N) (h : M →ₗ[R] Q) (x : AdicCompletion I M) :
    extension I f (AdicCompletion.map I h x) = extension I (f.comp h) x := by
  change (AdicCompletion.ofLinearEquiv I N).symm (AdicCompletion.map I f (AdicCompletion.map I h x)) = _
  rw [AdicCompletion.map_comp_apply]
  rfl

theorem postcompose [IsAdicComplete I P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (x : AdicCompletion I M) :
    g (extension I f x) = extension I (g.comp f) x := by
  apply (AdicCompletion.ofLinearEquiv I P).injective
  change AdicCompletion.of I P (g (extension I f x)) = AdicCompletion.of I P (extension I (g.comp f) x)
  rw [← AdicCompletion.map_of, of_extension, of_extension, AdicCompletion.map_comp_apply]

theorem square [IsAdicComplete I P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : M →ₗ[R] Q) (k : Q →ₗ[R] P) (hs : g.comp f = k.comp h) (x : AdicCompletion I M) :
    g (extension I f x) = extension I k (AdicCompletion.map I h x) := by
  rw [postcompose, hs, extension_map]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.LinearExtension
