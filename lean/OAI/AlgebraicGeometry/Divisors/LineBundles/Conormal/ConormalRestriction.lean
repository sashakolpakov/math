import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Conormal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual conormal and symmetric-algebra restriction maps -/

variable {R S : Type} [CommRing R] [CommRing S]

def cotangentCoefficientMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    I.Cotangent →ₛₗ[Ideal.quotientMap J f hf] J.Cotangent := by
  let : Algebra R S := f.toAlgebra
  let h : I.Cotangent →ₗ[R] J.Cotangent := Ideal.mapCotangent I J (Algebra.ofId R S) hf
  exact {
    toFun := h
    map_add' := h.map_add
    map_smul' := fun r m => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      rw [Ideal.quotientMap_mk]
      change h ((algebraMap R (R ⧸ I) r) • m) = (algebraMap S (S ⧸ J) (f r)) • h m
      rw [algebraMap_smul, map_smul, algebraMap_smul]
      rfl
  }

theorem cotangentCoefficientMap_toCotangent (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : I) :
    cotangentCoefficientMap I J f hf (I.toCotangent r) = J.toCotangent ⟨f r.val, hf r.property⟩ := rfl

def conormalSymmetricRestriction (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    SymmetricAlgebra (R ⧸ I) I.Cotangent →+* SymmetricAlgebra (S ⧸ J) J.Cotangent :=
  Symmetric.ScalarMap.BundleCycles.symmetricScalarMap (Ideal.quotientMap J f hf) (cotangentCoefficientMap I J f hf)

theorem conormalSymmetricRestriction_generator (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : I) :
    conormalSymmetricRestriction I J f hf (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent (I.toCotangent r)) =
      SymmetricAlgebra.ι (S ⧸ J) J.Cotangent (J.toCotangent ⟨f r.val, hf r.property⟩) :=
  Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator _ _ _

theorem conormalSymmetricRestriction_algebraMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : R ⧸ I) :
    conormalSymmetricRestriction I J f hf (algebraMap (R ⧸ I) (SymmetricAlgebra (R ⧸ I) I.Cotangent) r) =
      algebraMap (S ⧸ J) (SymmetricAlgebra (S ⧸ J) J.Cotangent) (Ideal.quotientMap J f hf r) :=
  Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap _ _ _

end

/-! # LineBundleCycles: identity and composition for actual conormal symmetric restrictions -/

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem conormalSymmetricRestriction_congr (I : Ideal R) (J : Ideal S)
    {f g : R →+* S} (h : f = g) (hf : I ≤ J.comap f) (hg : I ≤ J.comap g) :
    conormalSymmetricRestriction I J f hf = conormalSymmetricRestriction I J g hg := by
  subst g
  rfl

theorem conormalIdeal_le_comap_id (I : Ideal R) : I ≤ I.comap (RingHom.id R) := fun _ h => h

theorem conormalIdeal_le_comap_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    I ≤ K.comap (g.comp f) := fun _ h => hg (hf h)

theorem conormalSymmetricRestriction_id (I : Ideal R) :
    conormalSymmetricRestriction I I (RingHom.id R) (conormalIdeal_le_comap_id I) =
      RingHom.id (SymmetricAlgebra (R ⧸ I) I.Cotangent) := by
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    rw [conormalSymmetricRestriction_algebraMap I I (RingHom.id R) (conormalIdeal_le_comap_id I)]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  · intro a
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    rw [conormalSymmetricRestriction_generator I I (RingHom.id R) (conormalIdeal_le_comap_id I)]
    rfl

theorem conormalSymmetricRestriction_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : R →+* S) (g : S →+* T) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (conormalSymmetricRestriction J K g hg).comp (conormalSymmetricRestriction I J f hf) =
      conormalSymmetricRestriction I K (g.comp f) (conormalIdeal_le_comap_comp I J K f g hf hg) := by
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    change conormalSymmetricRestriction J K g hg
      (conormalSymmetricRestriction I J f hf (algebraMap _ _ a)) = _
    rw [conormalSymmetricRestriction_algebraMap I J f hf,
      conormalSymmetricRestriction_algebraMap J K g hg,
      conormalSymmetricRestriction_algebraMap I K (g.comp f) (conormalIdeal_le_comap_comp I J K f g hf hg)]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  · intro a
    obtain ⟨a, rfl⟩ := I.toCotangent_surjective a
    change conormalSymmetricRestriction J K g hg
      (conormalSymmetricRestriction I J f hf (SymmetricAlgebra.ι _ _ _)) = _
    rw [conormalSymmetricRestriction_generator I J f hf,
      conormalSymmetricRestriction_generator J K g hg,
      conormalSymmetricRestriction_generator I K (g.comp f) (conormalIdeal_le_comap_comp I J K f g hf hg)]
    rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction.BundleCycles
