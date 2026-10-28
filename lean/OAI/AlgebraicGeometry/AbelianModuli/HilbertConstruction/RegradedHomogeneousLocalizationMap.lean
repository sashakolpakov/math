import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Regraded Homogeneous Localization Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RegradedHomogeneousLocalizationMap

noncomputable section

/-! A ring map carrying degree d into degree φ(d) induces a map on
homogeneous localizations. The two numerator degrees change together. -/
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (g : ℕ → Submodule R A) (h : ℕ → Submodule R B) [GradedAlgebra g] [GradedAlgebra h]
variable (φ : ℕ → ℕ) (f : A →+* B) (hf : ∀ n x, x ∈ g n → f x ∈ h (φ n))
variable {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)

def regradedHomogeneousFraction (x : HomogeneousLocalization.NumDenSameDeg g P) :
    HomogeneousLocalization.NumDenSameDeg h Q where
  deg := φ x.deg
  num := ⟨f x.num, hf x.deg x.num x.num.property⟩
  den := ⟨f x.den, hf x.deg x.den x.den.property⟩
  den_mem := hPQ x.den_mem

def regradedHomogeneousLocalizationFun : HomogeneousLocalization g P → HomogeneousLocalization h Q :=
  Quotient.map' (regradedHomogeneousFraction g h φ f hf hPQ) (by
    intro x y he
    have he' := congrArg (IsLocalization.map (Localization Q) f hPQ) he
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.map_mk'] at he'
    change HomogeneousLocalization.NumDenSameDeg.embedding h Q
        (regradedHomogeneousFraction g h φ f hf hPQ x) =
      HomogeneousLocalization.NumDenSameDeg.embedding h Q
        (regradedHomogeneousFraction g h φ f hf hPQ y)
    simpa only [HomogeneousLocalization.NumDenSameDeg.embedding,
      regradedHomogeneousFraction, Localization.mk_eq_mk'] using he')

omit [GradedAlgebra g] [GradedAlgebra h] in
theorem regradedHomogeneousLocalizationFun_val (x : HomogeneousLocalization g P) :
    (regradedHomogeneousLocalizationFun g h φ f hf hPQ x).val =
      IsLocalization.map (Localization Q) f hPQ x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [regradedHomogeneousLocalizationFun, Quotient.map'_mk'',
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

def regradedHomogeneousLocalizationMap : HomogeneousLocalization g P →+* HomogeneousLocalization h Q where
  toFun := regradedHomogeneousLocalizationFun g h φ f hf hPQ
  map_one' := by
    apply HomogeneousLocalization.val_injective
    simp only [regradedHomogeneousLocalizationFun_val, HomogeneousLocalization.val_one, map_one]
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [regradedHomogeneousLocalizationFun_val, HomogeneousLocalization.val_zero, map_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [regradedHomogeneousLocalizationFun_val, HomogeneousLocalization.val_add, map_add]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [regradedHomogeneousLocalizationFun_val, HomogeneousLocalization.val_mul, map_mul]

theorem regradedHomogeneousLocalizationMap_mk (x : HomogeneousLocalization.NumDenSameDeg g P) :
    regradedHomogeneousLocalizationMap g h φ f hf hPQ (HomogeneousLocalization.mk x) =
      HomogeneousLocalization.mk (regradedHomogeneousFraction g h φ f hf hPQ x) := rfl

theorem regradedHomogeneousLocalizationMap_val (x : HomogeneousLocalization g P) :
    (regradedHomogeneousLocalizationMap g h φ f hf hPQ x).val =
      IsLocalization.map (Localization Q) f hPQ x.val :=
  regradedHomogeneousLocalizationFun_val g h φ f hf hPQ x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RegradedHomogeneousLocalizationMap
