import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension

/-! # Scalar Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual symmetric-algebra maps under a change of coefficient ring -/

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]

abbrev symmetricScalarAlgebra (f : R →+* S) : Algebra R (SymmetricAlgebra S N) :=
  ((algebraMap S (SymmetricAlgebra S N)).comp f).toAlgebra

def symmetricScalarLinear (f : R →+* S) (g : M →ₛₗ[f] N) :
    letI := symmetricScalarAlgebra (N := N) f
    M →ₗ[R] SymmetricAlgebra S N := by
  let := symmetricScalarAlgebra (N := N) f
  exact {
    toFun := fun m => SymmetricAlgebra.ι S N (g m)
    map_add' := fun m n => by rw [map_add, map_add]
    map_smul' := fun r m => by
      rw [g.map_smulₛₗ, map_smul]
      change f r • SymmetricAlgebra.ι S N (g m) = r • SymmetricAlgebra.ι S N (g m)
      simp only [Algebra.smul_def]
      rfl
  }

def symmetricScalarMapData (f : R →+* S) (g : M →ₛₗ[f] N) :
    {h : SymmetricAlgebra R M →+* SymmetricAlgebra S N //
      (∀ m, h (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (g m)) ∧
      ∀ r, h (algebraMap R (SymmetricAlgebra R M) r) = algebraMap S (SymmetricAlgebra S N) (f r)} := by
  let e := @Extension.BundleCycles.symmetricExtension R M (SymmetricAlgebra S N) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) (symmetricScalarAlgebra f)
    (symmetricScalarLinear f g)
  exact ⟨e.val, e.property.1, e.property.2⟩

def symmetricScalarMap (f : R →+* S) (g : M →ₛₗ[f] N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  (symmetricScalarMapData f g).val

theorem symmetricScalarMap_generator (f : R →+* S) (g : M →ₛₗ[f] N) (m : M) :
    symmetricScalarMap f g (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (g m) :=
  (symmetricScalarMapData f g).property.1 m

theorem symmetricScalarMap_algebraMap (f : R →+* S) (g : M →ₛₗ[f] N) (r : R) :
    symmetricScalarMap f g (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (f r) :=
  (symmetricScalarMapData f g).property.2 r

theorem symmetricRingHom_ext {T : Type} [CommRing T]
    (f g : SymmetricAlgebra R M →+* T)
    (hc : ∀ r, f (algebraMap R (SymmetricAlgebra R M) r) = g (algebraMap R (SymmetricAlgebra R M) r))
    (hm : ∀ m, f (SymmetricAlgebra.ι R M m) = g (SymmetricAlgebra.ι R M m)) : f = g := by
  apply RingHom.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact hc r
  | ι m => exact hm m
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap.BundleCycles
