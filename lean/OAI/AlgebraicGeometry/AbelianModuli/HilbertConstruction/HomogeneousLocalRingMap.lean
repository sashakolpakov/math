import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RegradedHomogeneousLocalizationMap

/-! # Homogeneous Local Ring Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogeneousLocalRingMap

noncomputable section

/-! Regraded homogeneous localization maps are local at corresponding
prime ideals. This supplies the stalk maps for the Veronese morphism. -/
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (g : ℕ → Submodule R A) (h : ℕ → Submodule R B) [GradedAlgebra g] [GradedAlgebra h]
variable (φ : ℕ → ℕ) (f : A →+* B) (hf : ∀ n x, x ∈ g n → f x ∈ h (φ n))
variable (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f)

def regradedHomogeneousLocalRingMap :
    HomogeneousLocalization.AtPrime g I →+* HomogeneousLocalization.AtPrime h J :=
  RegradedHomogeneousLocalizationMap.regradedHomogeneousLocalizationMap g h φ f hf
    (Localization.le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

theorem regradedHomogeneousLocalRingMap_val (x : HomogeneousLocalization.AtPrime g I) :
    (regradedHomogeneousLocalRingMap g h φ f hf I J hIJ x).val =
      Localization.localRingHom I J f hIJ x.val :=
  RegradedHomogeneousLocalizationMap.regradedHomogeneousLocalizationMap_val g h φ f hf _ x

instance regradedHomogeneousLocalRingMap_isLocalHom :
    IsLocalHom (regradedHomogeneousLocalRingMap g h φ f hf I J hIJ) where
  map_nonunit x hx := by
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hx ⊢
    rw [regradedHomogeneousLocalRingMap_val] at hx
    exact IsLocalHom.map_nonunit _ hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogeneousLocalRingMap
