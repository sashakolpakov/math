import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPlaneGroups

/-! # Unitary Basis Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM

noncomputable section

section

/-! Actual field-coordinate equivalences of special-unitary groups,
including surjectivity and the determinant-one condition. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
  {n : Type*} [Fintype n] [DecidableEq n]

def specialUnitaryFieldMap (f : R →+* S) (hf : ∀ x, f (star x) = star (f x))
    (H : Matrix n n R) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) where
  toFun g := ⟨(RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H g)).val,
    (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H g)).property, by
      apply Units.ext
      change (g.val.val.map f).det = 1
      have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
      have hm : f g.val.val.det = (g.val.val.map f).det := f.map_det g.val.val
      rw [← hm, hd, map_one]⟩
  map_one' := by
    apply Subtype.ext
    change (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H 1)).val = 1
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    change (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H (g * h))).val =
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H g)).val *
        (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H h)).val
    rw [map_mul, map_mul]
    rfl

theorem special_unitary_field_map_injective (f : R →+* S) (hf : ∀ x, f (star x) = star (f x))
    (hi : Function.Injective f) (H : Matrix n n R) :
    Function.Injective (specialUnitaryFieldMap f hf H) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply hi
  exact congrArg (fun u : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) => u.val.val i j) he

theorem special_unitary_field_map_surjective (e : R ≃+* S)
    (he : ∀ x, e (star x) = star (e x)) (H : Matrix n n R) :
    Function.Surjective (specialUnitaryFieldMap e.toRingHom he H) := by
  intro g
  let u : (Matrix n n R)ˣ := Units.map e.symm.toRingHom.mapMatrix.toMonoidHom g.val
  have hu : u.val.map e.toRingHom = g.val.val := by
    apply Matrix.ext
    intro i j
    exact e.apply_symm_apply _
  have hf : u.val.conjTranspose * H * u.val = H := by
    apply e.mapMatrix.injective
    change (u.val.conjTranspose * H * u.val).map e.toRingHom = H.map e.toRingHom
    rw [Matrix.map_mul, Matrix.map_mul, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.map_conjTranspose e.toRingHom he, hu]
    exact g.property.1
  have hd : Matrix.GeneralLinearGroup.det u = 1 := by
    apply Units.ext
    apply e.injective
    change e u.val.det = e 1
    have hm : e u.val.det = (u.val.map e.toRingHom).det := e.map_det u.val
    rw [hm, hu, map_one]
    exact congrArg Units.val g.property.2
  refine ⟨⟨u, hf, hd⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hu

def specialUnitaryFieldEquiv (e : R ≃+* S)
    (he : ∀ x, e (star x) = star (e x)) (H : Matrix n n R) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map e.toRingHom) :=
  MulEquiv.ofBijective (specialUnitaryFieldMap e.toRingHom he H)
    ⟨special_unitary_field_map_injective e.toRingHom he e.injective H,
      special_unitary_field_map_surjective e he H⟩

end

/-! Special-unitary groups in the actual original and normalized
Hermitian bases are isomorphic by matrix conjugation. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_basis_inverse (H H₀ : Matrix n n ℂ) (B : (Matrix n n ℂ)ˣ)
    (hB : B.val.conjTranspose * H * B.val = H₀) :
    B.inv.conjTranspose * H₀ * B.inv = H := by
  rw [← hB]
  calc
    _ = (B.inv.conjTranspose * B.val.conjTranspose) * H * (B.val * B.inv) := by noncomm_ring
    _ = H := by
      rw [← Matrix.conjTranspose_mul, B.val_inv, Matrix.conjTranspose_one, one_mul, mul_one]

theorem unitary_basis_preserves (H H₀ G : Matrix n n ℂ) (B : (Matrix n n ℂ)ˣ)
    (hB : B.val.conjTranspose * H * B.val = H₀) (hG : G.conjTranspose * H * G = H) :
    (B.inv * G * B.val).conjTranspose * H₀ * (B.inv * G * B.val) = H₀ := by
  calc
    _ = B.val.conjTranspose * (G.conjTranspose * (B.inv.conjTranspose * H₀ * B.inv) * G) *
        B.val := by
      simp only [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = H₀ := by rw [unitary_basis_inverse H H₀ B hB, hG, hB]

def specialUnitaryBasisHom (H H₀ : Matrix n n ℂ) (B : (Matrix n n ℂ)ˣ)
    (hB : B.val.conjTranspose * H * B.val = H₀) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H₀ where
  toFun g := ⟨B⁻¹ * g.val * B, by
    constructor
    · exact unitary_basis_preserves H H₀ g.val.val B hB g.property.1
    · change Matrix.GeneralLinearGroup.det (B⁻¹ * g.val * B) = 1
      rw [map_mul, map_mul, map_inv, g.property.2, mul_one, inv_mul_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

theorem special_unitary_basis_hom_bijective (H H₀ : Matrix n n ℂ) (B : (Matrix n n ℂ)ˣ)
    (hB : B.val.conjTranspose * H * B.val = H₀) :
    Function.Bijective (specialUnitaryBasisHom H H₀ B hB) := by
  constructor
  · intro g h he
    apply Subtype.ext
    have hu : B⁻¹ * g.val * B = B⁻¹ * h.val * B := congrArg Subtype.val he
    exact mul_left_cancel (mul_right_cancel hu)
  · intro g
    let h := specialUnitaryBasisHom H₀ H B⁻¹ (unitary_basis_inverse H H₀ B hB) g
    refine ⟨h, ?_⟩
    apply Subtype.ext
    change B⁻¹ * ((B⁻¹)⁻¹ * g.val * B⁻¹) * B = g.val
    group

def specialUnitaryBasisEquiv (H H₀ : Matrix n n ℂ) (B : (Matrix n n ℂ)ˣ)
    (hB : B.val.conjTranspose * H * B.val = H₀) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H₀ :=
  MulEquiv.ofBijective (specialUnitaryBasisHom H H₀ B hB)
    (special_unitary_basis_hom_bijective H H₀ B hB)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates.CM
