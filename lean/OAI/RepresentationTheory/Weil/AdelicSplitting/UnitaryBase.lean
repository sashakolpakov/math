import Mathlib

/-! # Unitary Base -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction

noncomputable section

/-! Full unitary isometry groups of specified forms, their scalar-extension
maps, and the tensor-product dual-pair action. These constructions work over
split quadratic algebras as well as quadratic fields. -/

open scoped Classical _root_.Matrix Kronecker

section Unitary
variable {R S : Type*} [CommRing R] [StarRing R]
  [CommRing S] [StarRing S]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def unitaryIsometries (H : Matrix n n R) : Subgroup (Matrix n n R)ˣ where
  carrier := {g | g.val.conjTranspose * H * g.val = H}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g.val * h.val).conjTranspose * H * (g.val * h.val) = H
    rw [Matrix.conjTranspose_mul]
    calc
      (h.val.conjTranspose * g.val.conjTranspose) * H * (g.val * h.val) =
          h.val.conjTranspose * (g.val.conjTranspose * H * g.val) * h.val := by
        simp only [mul_assoc]
      _ = H := by rw [hg, hh]
  inv_mem' := by
    intro g hg
    change (g⁻¹).val.conjTranspose * H * (g⁻¹).val = H
    have hc : (g⁻¹).val.conjTranspose * g.val.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, ← Units.val_mul, mul_inv_cancel]
      simp
    calc
      (g⁻¹).val.conjTranspose * H * (g⁻¹).val =
          (g⁻¹).val.conjTranspose * (g.val.conjTranspose * H * g.val) * (g⁻¹).val := by
        rw [hg]
      _ = ((g⁻¹).val.conjTranspose * g.val.conjTranspose) * H *
          (g.val * (g⁻¹).val) := by simp only [mul_assoc]
      _ = H := by rw [hc, ← Units.val_mul, mul_inv_cancel]; simp

abbrev Unitary (H : Matrix n n R) := unitaryIsometries H

def unitaryMatrix (H : Matrix n n R) : Construction.Unitary H →* (Matrix n n R)ˣ :=
  (unitaryIsometries H).subtype

theorem unitary_preserves (H : Matrix n n R) (g : Construction.Unitary H) :
    g.val.val.conjTranspose * H * g.val.val = H := g.property

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem map_conjTranspose (f : R →+* S) (hf : ∀ x, f (star x) = star (f x))
    (A : Matrix n m R) : A.conjTranspose.map f = (A.map f).conjTranspose := by
  ext i j
  exact hf (A j i)

def unitaryBaseChange (f : R →+* S) (hf : ∀ x, f (star x) = star (f x))
    (H : Matrix n n R) : Construction.Unitary H →* Construction.Unitary (H.map f) where
  toFun g := ⟨Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom g.val, by
    change (g.val.val.map f).conjTranspose * H.map f * g.val.val.map f = H.map f
    have h := congrArg (fun A : Matrix n n R => A.map f) g.property
    simpa only [Matrix.map_mul, map_conjTranspose f hf] using h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

@[simp] theorem unitaryBaseChange_matrix (f : R →+* S)
    (hf : ∀ x, f (star x) = star (f x)) (H : Matrix n n R) (g : Construction.Unitary H) :
    (unitaryBaseChange f hf H g).val.val = g.val.val.map f := rfl

def tensorUnits (g : (Matrix n n R)ˣ) (h : (Matrix m m R)ˣ) :
    (Matrix (n × m) (n × m) R)ˣ where
  val := g.val ⊗ₖ h.val
  inv := g.inv ⊗ₖ h.inv
  val_inv := by rw [← Matrix.mul_kronecker_mul, g.val_inv, h.val_inv]; simp
  inv_val := by rw [← Matrix.mul_kronecker_mul, g.inv_val, h.inv_val]; simp

/-- The full product acts on the tensor-product form by Kronecker matrices. -/
def unitaryTensor (H : Matrix n n R) (K : Matrix m m R) :
    Construction.Unitary H × Construction.Unitary K →* Construction.Unitary (H ⊗ₖ K) where
  toFun g := ⟨tensorUnits g.1.val g.2.val, by
    change (g.1.val.val ⊗ₖ g.2.val.val).conjTranspose * (H ⊗ₖ K) *
      (g.1.val.val ⊗ₖ g.2.val.val) = H ⊗ₖ K
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, g.1.property, g.2.property]⟩
  map_one' := by apply Subtype.ext; apply Units.ext; exact Matrix.one_kronecker_one
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    exact Matrix.mul_kronecker_mul _ _ _ _

theorem unitaryTensor_preserves (H : Matrix n n R) (K : Matrix m m R)
    (g : Construction.Unitary H × Construction.Unitary K) :
    (unitaryTensor H K g).val.val.conjTranspose * (H ⊗ₖ K) *
      (unitaryTensor H K g).val.val = H ⊗ₖ K :=
  (unitaryTensor H K g).property

end Unitary

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev Quadratic (R : Type*) [CommRing R] (d : R) := QuadraticAlgebra R d 0

def quadraticBaseChange (f : R →+* S) (d : R) : Construction.Quadratic R d →+* Construction.Quadratic S (f d) where
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by ext <;> simp [map_add]
  map_mul' z w := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul]

theorem quadraticBaseChange_star (f : R →+* S) (d : R) (z : Construction.Quadratic R d) :
    quadraticBaseChange f d (star z) = star (quadraticBaseChange f d z) := by
  ext <;> simp [quadraticBaseChange, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem quadraticBaseChange_norm (f : R →+* S) (d : R) (z : Construction.Quadratic R d) :
    QuadraticAlgebra.norm (quadraticBaseChange f d z) = f (QuadraticAlgebra.norm z) := by
  simp [QuadraticAlgebra.norm_def, quadraticBaseChange, map_sub, map_mul]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction
