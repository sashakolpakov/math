import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Ideal Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IdealFunctoriality

noncomputable section

/-! On affine schemes, ideal-sheaf image and inverse image are contraction and extension of ring ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- The global ideal of the scheme-theoretic image is the kernel of the map on global functions. -/
theorem affine_kernel_ideal [IsAffine X] (f : Y ⟶ X) :
    Scheme.IdealSheafData.equivOfIsAffine f.ker = RingHom.ker f.appTop.hom := by
  rw [Scheme.ker_of_isAffine]
  simp

/-- The canonical closed inclusion has the prescribed kernel on global functions. -/
theorem affine_subscheme_kernel [IsAffine X] (I : X.IdealSheafData) :
    RingHom.ker I.subschemeι.appTop.hom = Scheme.IdealSheafData.equivOfIsAffine I :=
  (affine_kernel_ideal I.subschemeι).symm.trans
    (congrArg Scheme.IdealSheafData.equivOfIsAffine I.ker_subschemeι)

/-- Image of an ideal sheaf is contraction along the map of affine coordinate rings. -/
theorem affine_ideal_map [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (I : X.IdealSheafData) :
    Scheme.IdealSheafData.equivOfIsAffine (I.map f) =
      (Scheme.IdealSheafData.equivOfIsAffine I).comap f.appTop.hom := by
  change Scheme.IdealSheafData.equivOfIsAffine (I.subschemeι ≫ f).ker = _
  rw [affine_kernel_ideal]
  have he : (I.subschemeι ≫ f).appTop.hom = I.subschemeι.appTop.hom.comp f.appTop.hom := by
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.comp_appTop I.subschemeι f)
  rw [he, ← RingHom.comap_ker, affine_subscheme_kernel]

/-- Inverse image of an ideal sheaf is extension along the map of affine coordinate rings. -/
theorem affine_ideal_comap [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (I : Y.IdealSheafData) :
    Scheme.IdealSheafData.equivOfIsAffine (I.comap f) =
      (Scheme.IdealSheafData.equivOfIsAffine I).map f.appTop.hom := by
  let EX := Scheme.IdealSheafData.equivOfIsAffine (X := X)
  let EY := Scheme.IdealSheafData.equivOfIsAffine (X := Y)
  have hiff : ∀ J : X.IdealSheafData,
      EX (I.comap f) ≤ EX J ↔ (EY I).map f.appTop.hom ≤ EX J := by
    intro J
    rw [map_le_map_iff EX, ← Scheme.IdealSheafData.le_map_iff_comap_le, Ideal.map_le_iff_le_comap]
    have he : EY (J.map f) = (EX J).comap f.appTop.hom := affine_ideal_map f J
    rw [← he]
    exact (map_le_map_iff EY).symm
  apply le_antisymm
  · have h := (hiff (EX.symm ((EY I).map f.appTop.hom))).mpr
      (le_of_eq (EX.apply_symm_apply _).symm)
    exact h.trans_eq (EX.apply_symm_apply _)
  · exact (hiff (I.comap f)).mp le_rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IdealFunctoriality
