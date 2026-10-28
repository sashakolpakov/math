import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Special Unitary Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange.Approximation

noncomputable section

section

/-! Continuous scalar extension of determinant-one unitary matrices
along a specified homomorphism that preserves conjugation. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
  {n : Type*} [Fintype n] [DecidableEq n]
  (f : R →+* S) (hf : ∀ x, f (star x) = star (f x)) (H : Matrix n n R)

def specialUnitaryBaseChange : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) where
  toFun g := ⟨Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom g.val,
    (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange f hf H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H g)).property, by
      apply Units.ext
      change (g.val.val.map f).det = 1
      have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
      exact (f.map_det g.val.val).symm.trans ((congrArg f hd).trans (map_one f))⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

theorem specialUnitaryBaseChange_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) :
    (specialUnitaryBaseChange f hf H g).val.val = g.val.val.map f := rfl

variable [TopologicalSpace R] [TopologicalSpace S]

theorem specialUnitaryBaseChange_continuous (hfc : Continuous f) :
    Continuous (specialUnitaryBaseChange f hf H) := by
  have hm : Continuous (f.mapMatrix : Matrix n n R →+* Matrix n n S) :=
    continuous_pi (fun i => continuous_pi (fun j =>
      hfc.comp ((continuous_apply j).comp (continuous_apply i))))
  have hu : Continuous (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom) :=
    hm.units_map _
  exact (hu.comp continuous_subtype_val).subtype_mk _

def specialUnitaryBaseChangeContinuous (hfc : Continuous f) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H →ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) :=
  ⟨specialUnitaryBaseChange f hf H, specialUnitaryBaseChange_continuous f hf H hfc⟩

end

/-! A specified continuous ring equivalence preserving conjugation
induces a continuous equivalence of the actual special unitary groups. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
  {n : Type*} [Fintype n] [DecidableEq n]
  (f : R ≃+* S) (hf : ∀ x, f (star x) = star (f x)) (H : Matrix n n R)

theorem specialUnitaryBaseChange_bijective :
    Function.Bijective (specialUnitaryBaseChange f.toRingHom hf H) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply f.injective
    exact congrArg (fun x : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) => x.val.val i j) he
  · intro g
    have hfi (x : S) : f.symm (star x) = star (f.symm x) := by
      apply f.injective
      rw [f.apply_symm_apply, hf, f.apply_symm_apply]
    have hH : (H.map f).map f.symm = H := by
      apply Matrix.ext
      intro i j
      exact f.symm_apply_apply (H i j)
    let x := specialUnitaryBaseChange f.symm.toRingHom hfi (H.map f) g
    have hx : x.val ∈ RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary H := by
      have hform := x.property.1
      change x.val.val.conjTranspose * ((H.map f).map f.symm) * x.val.val =
        (H.map f).map f.symm at hform
      rw [hH] at hform
      exact ⟨hform, x.property.2⟩
    refine ⟨⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact f.apply_symm_apply (g.val.val i j)

def specialUnitaryScalarEquiv : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) :=
  MulEquiv.ofBijective (specialUnitaryBaseChange f.toRingHom hf H)
    (specialUnitaryBaseChange_bijective f hf H)

theorem specialUnitaryScalarEquiv_symm_units (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f)) :
    ((specialUnitaryScalarEquiv f hf H).symm g).val =
      Units.map f.symm.toRingHom.mapMatrix.toMonoidHom g.val := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h := congrArg (fun x : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) => x.val.val i j)
    ((specialUnitaryScalarEquiv f hf H).apply_symm_apply g)
  change f (((specialUnitaryScalarEquiv f hf H).symm g).val.val i j) = g.val.val i j at h
  exact (f.symm_apply_apply _).symm.trans (congrArg f.symm h)

variable [TopologicalSpace R] [TopologicalSpace S]

theorem specialUnitaryScalarEquiv_symm_continuous (hfc : Continuous f.symm) :
    Continuous (specialUnitaryScalarEquiv f hf H).symm := by
  have hm : Continuous (f.symm.toRingHom.mapMatrix : Matrix n n S →+* Matrix n n R) :=
    continuous_pi (fun i => continuous_pi (fun j =>
      hfc.comp ((continuous_apply j).comp (continuous_apply i))))
  have hu : Continuous (fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) =>
      Units.map f.symm.toRingHom.mapMatrix.toMonoidHom g.val) :=
    (hm.units_map _).comp continuous_subtype_val
  exact (hu.congr (fun g => (specialUnitaryScalarEquiv_symm_units f hf H g).symm)).subtype_mk _

def specialUnitaryScalarHomeomorph (hfc : Continuous f) (hfic : Continuous f.symm) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.map f) where
  __ := specialUnitaryScalarEquiv f hf H
  continuous_toFun := specialUnitaryBaseChange_continuous f.toRingHom hf H hfc
  continuous_invFun := specialUnitaryScalarEquiv_symm_continuous f hf H hfic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange.Approximation
