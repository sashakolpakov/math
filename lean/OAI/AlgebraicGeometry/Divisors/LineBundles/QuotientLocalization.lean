import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of a quotient ring

Quotienting by an ideal commutes with localization. The proof follows
numerators and denominators explicitly and will be applied to the parameter
ideal of the deformation, in order to glue its normal-cone fibers.
-/

universe u v
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The actual quotient map induced by localization of coefficients. -/
def quotientLocalizationMap (I : Ideal R) : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMap _ (algebraMap R S) (fun _ hr => Ideal.mem_map_of_mem _ hr)

@[simp]
theorem quotientLocalizationMap_mk (I : Ideal R) (r : R) :
    quotientLocalizationMap S I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := rfl

/-- The quotient after localization is a localization of the original quotient. -/
theorem quotientLocalizationMap_isLocalization (I : Ideal R) :
    letI := (quotientLocalizationMap S I).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (S ⧸ I.map (algebraMap R S)) := by
  let := (quotientLocalizationMap S I).toAlgebra
  let J := I.map (algebraMap R S)
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨q, ⟨m, hm, rfl⟩⟩
    change IsUnit (Ideal.Quotient.mk J (algebraMap R S m))
    exact (IsLocalization.map_units S (⟨m, hm⟩ : M)).map (Ideal.Quotient.mk J)
  · intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨⟨x, m⟩, he⟩ := IsLocalization.surj M y
    refine ⟨(Ideal.Quotient.mk I x,
      ⟨Ideal.Quotient.mk I m.val, Submonoid.mem_map_of_mem _ m.property⟩), ?_⟩
    change Ideal.Quotient.mk J y * Ideal.Quotient.mk J (algebraMap R S m.val) =
      Ideal.Quotient.mk J (algebraMap R S x)
    exact (map_mul (Ideal.Quotient.mk J) y (algebraMap R S m.val)).symm.trans
      (congrArg (Ideal.Quotient.mk J) he)
  · intro p q he
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective p
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hxy : algebraMap R S (x - y) ∈ J := by
      rw [map_sub]
      exact Ideal.Quotient.eq.mp he
    obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I (x - y)).mp hxy
    refine ⟨⟨Ideal.Quotient.mk I m, Submonoid.mem_map_of_mem _ hm⟩, ?_⟩
    change Ideal.Quotient.mk I m * Ideal.Quotient.mk I x =
      Ideal.Quotient.mk I m * Ideal.Quotient.mk I y
    rw [← map_mul, ← map_mul]
    apply Ideal.Quotient.eq.mpr
    exact (mul_sub m x y) ▸ hmem

/-- The same localization statement with the target ideal supplied by its
actual image equality, as needed for gluing affine ideal presentations. -/
theorem quotientMap_isLocalization (I : Ideal R) (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI := (Ideal.quotientMap J (algebraMap R S) hIJ).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (S ⧸ J) := by
  subst J
  exact quotientLocalizationMap_isLocalization M S I

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization.BundleCycles
