import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Contragredient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local

noncomputable section

/-! The inverse-transpose automorphism of the actual special-linear
group preserves the literal integral level. -/

open scoped Classical

variable (R : Type*) [CommRing R]

def contragredient : Matrix.SpecialLinearGroup (Fin 3) R →*
    Matrix.SpecialLinearGroup (Fin 3) R where
  toFun g := (g⁻¹).transpose
  map_one' := by
    apply Subtype.ext
    simp only [inv_one, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  map_mul' g h := by
    apply Subtype.ext
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem contragredient_involutive : Function.Involutive (contragredient R) := by
  intro g
  change ((contragredient R g)⁻¹).transpose = g
  rw [← map_inv]
  change (((g⁻¹)⁻¹).transpose).transpose = g
  rw [inv_inv]
  rfl

def contragredientEquiv : Matrix.SpecialLinearGroup (Fin 3) R ≃*
    Matrix.SpecialLinearGroup (Fin 3) R :=
  { (contragredient_involutive R).toPerm _ with map_mul' := (contragredient R).map_mul }

theorem contragredient_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    contragredient S (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (contragredient R g) := by
  change ((Matrix.SpecialLinearGroup.map f g)⁻¹).transpose = _
  rw [← map_inv]
  rfl

theorem contragredient_integral (q : ℕ) [Fact q.Prime] (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    contragredient ℚ_[q] g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  obtain ⟨a, rfl⟩ := hg
  exact ⟨contragredient ℤ_[q] a, (contragredient_map ℤ_[q] PadicInt.Coe.ringHom a).symm⟩

theorem contragredient_integral_iff (q : ℕ) [Fact q.Prime] (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    contragredient ℚ_[q] g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ↔ g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q := by
  constructor
  · intro h
    simpa only [contragredient_involutive ℚ_[q] g] using contragredient_integral q _ h
  · exact contragredient_integral q g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local
