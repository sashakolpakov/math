import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EtaleCotangentCriterion
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Quotient Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.QuotientCriterion

noncomputable section

/-! A smooth quotient of a local noetherian algebra cannot retain
the same tangent dimension unless the quotient is an isomorphism.
The argument uses the actual map on differentials and Nakayama's lemma,
so it also detects nilpotents in the original algebra. -/

open scoped TensorProduct

theorem localModule_injective_of_residue_finrank_le
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hd : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] N)) :
    Function.Injective f := by
  let k := IsLocalRing.ResidueField R
  have hbase : Function.Injective (f.baseChange k) :=
    (OrzechProperty.bijective_of_surjective_of_finrank_le
      (f.baseChange k) (f.lTensor_surjective k hf) hd).injective
  obtain ⟨g, hg⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hbase
  exact Function.HasLeftInverse.injective ⟨g, LinearMap.congr_fun hg⟩

/-- Coefficient-valued derivations are the dual of the actual fiber of
the module of differentials, with the original coefficient scalar action. -/
def coefficientDifferentialDualEquiv
    (k A C : Type*) [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C] :
    (C ⊗[A] Ω[A⁄k] →ₗ[C] C) ≃ₗ[C] Derivation k A C := by
  let e : (Ω[A⁄k] →ₗ[A] C) ≃ₗ[C] Derivation k A C :=
    { (KaehlerDifferential.linearMapEquivDerivation k A).toEquiv with
      map_add' f g := (KaehlerDifferential.linearMapEquivDerivation k A).map_add f g
      map_smul' c f := by
        apply Derivation.ext
        intro a
        rfl }
  exact (LinearMap.liftBaseChangeEquiv C).symm.trans e

theorem coefficientDifferential_finrank_eq_derivations
    (k A F : Type*) [CommRing k] [CommRing A] [Field F]
    [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F] :
    Module.finrank F (F ⊗[A] Ω[A⁄k]) = Module.finrank F (Derivation k A F) := by
  rw [← Subspace.dual_finrank_eq]
  exact (coefficientDifferentialDualEquiv k A F).finrank_eq

section General

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsLocalRing B] [Algebra.EssFiniteType k A] [Algebra.EssFiniteType k B]
    [Algebra.FormallySmooth k B]
    (hAB : Function.Surjective (algebraMap A B))
    (hd : Module.finrank (IsLocalRing.ResidueField B)
        (IsLocalRing.ResidueField B ⊗[B] (B ⊗[A] Ω[A⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField B)
        (IsLocalRing.ResidueField B ⊗[B] Ω[B⁄k]))

include hAB hd in
theorem smoothQuotient_cotangent_injective :
    Function.Injective (KaehlerDifferential.mapBaseChange k A B) := by
  let : Module.Free B Ω[B⁄k] := Module.free_of_flat_of_isLocalRing
  exact localModule_injective_of_residue_finrank_le
    (KaehlerDifferential.mapBaseChange k A B)
    (KaehlerDifferential.mapBaseChange_surjective k A B hAB) hd

include hAB hd in
theorem smoothQuotient_formallyEtale : Algebra.FormallyEtale A B := by
  let : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId A B) hAB
  exact HilbertConstruction.EtaleCotangentCriterion.formallyEtale_of_cotangent_injective k A B
    (smoothQuotient_cotangent_injective k A B hAB hd)

include hAB hd in
theorem smoothQuotient_algebraMap_bijective [IsLocalRing A] [IsNoetherianRing A] :
    Function.Bijective (algebraMap A B) := by
  have hE := smoothQuotient_formallyEtale k A B hAB hd
  have hI := (Algebra.FormallyEtale.iff_of_surjective hAB).mp hE
  have hzero : RingHom.ker (algebraMap A B) = ⊥ :=
    ((Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).mp hI).resolve_right
      (RingHom.ker_ne_top (algebraMap A B))
  exact ⟨(RingHom.injective_iff_ker_eq_bot _).mpr hzero, hAB⟩

include hAB hd in
theorem smoothQuotient_source_formallySmooth [IsLocalRing A] [IsNoetherianRing A] :
    Algebra.FormallySmooth k A := by
  let e : A ≃ₐ[k] B := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k A B)
    (smoothQuotient_algebraMap_bijective k A B hAB hd)
  exact Algebra.FormallySmooth.of_equiv e.symm

include hAB in
theorem smoothQuotient_source_formallySmooth_of_derivations
    [IsLocalRing A] [IsNoetherianRing A]
    (hderiv : Module.finrank (IsLocalRing.ResidueField B)
        (Derivation k A (IsLocalRing.ResidueField B)) ≤
      Module.finrank (IsLocalRing.ResidueField B)
        (Derivation k B (IsLocalRing.ResidueField B))) :
    Algebra.FormallySmooth k A := by
  apply smoothQuotient_source_formallySmooth k A B hAB
  calc
    _ = Module.finrank (IsLocalRing.ResidueField B)
        (IsLocalRing.ResidueField B ⊗[A] Ω[A⁄k]) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B
        (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B) Ω[A⁄k]).finrank_eq
    _ = Module.finrank (IsLocalRing.ResidueField B)
        (Derivation k A (IsLocalRing.ResidueField B)) :=
      coefficientDifferential_finrank_eq_derivations k A (IsLocalRing.ResidueField B)
    _ ≤ Module.finrank (IsLocalRing.ResidueField B)
        (Derivation k B (IsLocalRing.ResidueField B)) := hderiv
    _ = _ := (coefficientDifferential_finrank_eq_derivations k B
      (IsLocalRing.ResidueField B)).symm

end General

/-- An augmentation of a local algebra identifies residue-field tensor
dimension with tensor dimension over the original coefficient field. -/
theorem augmentedResidueTensor_finrank
    (k B V : Type*) [Field k] [CommRing B] [IsLocalRing B]
    [Algebra k B] [Algebra B k] [IsScalarTower k B k]
    [AddCommGroup V] [Module B V] [Module.Finite B V] :
    Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B ⊗[B] V) =
      Module.finrank k (k ⊗[B] V) := by
  have hs : Function.Surjective (algebraMap B k) := by
    intro c
    refine ⟨algebraMap k B c, ?_⟩
    simpa using (IsScalarTower.algebraMap_apply k B k c).symm
  have hker := IsLocalRing.ker_eq_maximalIdeal (algebraMap B k) hs
  let e : IsLocalRing.ResidueField B ≃ₐ[B] k :=
    (Ideal.quotientEquivAlgOfEq B hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId B k) hs)
  let : Algebra (IsLocalRing.ResidueField B) k := e.toRingHom.toAlgebra
  let : IsScalarTower B (IsLocalRing.ResidueField B) k :=
    IsScalarTower.of_algebraMap_eq (fun b => (e.commutes b).symm)
  have h := (TensorProduct.AlgebraTensorModule.cancelBaseChange B
    (IsLocalRing.ResidueField B) k k V).finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h

/-- A smooth augmented quotient with no smaller tangent space is the
original local algebra itself, including its possible nilpotents. -/
theorem augmentedSmoothQuotient_algebraMap_bijective
    (k A B : Type*) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra A k] [Algebra B k] [IsScalarTower k A k]
    [IsScalarTower k B k] [IsScalarTower A B k]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B]
    [Algebra.EssFiniteType k A] [Algebra.EssFiniteType k B]
    [Algebra.FormallySmooth k B]
    (hAB : Function.Surjective (algebraMap A B))
    (hderiv : Module.finrank k (Derivation k A k) ≤ Module.finrank k (Derivation k B k)) :
    Function.Bijective (algebraMap A B) := by
  apply smoothQuotient_algebraMap_bijective k A B hAB
  calc
    _ = Module.finrank k (k ⊗[B] (B ⊗[A] Ω[A⁄k])) :=
      augmentedResidueTensor_finrank k B (B ⊗[A] Ω[A⁄k])
    _ = Module.finrank k (k ⊗[A] Ω[A⁄k]) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k Ω[A⁄k]).finrank_eq
    _ = Module.finrank k (Derivation k A k) :=
      coefficientDifferential_finrank_eq_derivations k A k
    _ ≤ Module.finrank k (Derivation k B k) := hderiv
    _ = Module.finrank k (k ⊗[B] Ω[B⁄k]) :=
      (coefficientDifferential_finrank_eq_derivations k B k).symm
    _ = _ := (augmentedResidueTensor_finrank k B Ω[B⁄k]).symm

/-- A local noetherian algebra with a smooth augmented quotient is
formally smooth when its coefficient-valued tangent space is no larger
than that quotient's tangent space. -/
theorem augmentedSmoothQuotient_source_formallySmooth
    (k A B : Type*) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra A k] [Algebra B k] [IsScalarTower k A k]
    [IsScalarTower k B k] [IsScalarTower A B k]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B]
    [Algebra.EssFiniteType k A] [Algebra.EssFiniteType k B]
    [Algebra.FormallySmooth k B]
    (hAB : Function.Surjective (algebraMap A B))
    (hderiv : Module.finrank k (Derivation k A k) ≤ Module.finrank k (Derivation k B k)) :
    Algebra.FormallySmooth k A := by
  let e : A ≃ₐ[k] B := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k A B)
    (augmentedSmoothQuotient_algebraMap_bijective k A B hAB hderiv)
  exact Algebra.FormallySmooth.of_equiv e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.QuotientCriterion
