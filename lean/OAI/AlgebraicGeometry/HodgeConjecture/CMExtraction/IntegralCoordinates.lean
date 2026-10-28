import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Integral Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport

noncomputable section

/-! The literal integral special-linear subgroup is characterized by
its matrix entries and by preservation of integral coordinate vectors. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem integralSL3_iff_entries (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ↔ ∀ i j, ‖g.val i j‖ ≤ 1 := by
  constructor
  · rintro ⟨a, rfl⟩ i j
    exact (a.val i j).property
  · intro hg
    let a : Matrix (Fin 3) (Fin 3) (PadicInt q) := fun i j => ⟨g.val i j, hg i j⟩
    have ha : a.det = 1 := by
      apply PadicInt.ext
      change (PadicInt.Coe.ringHom (p := q)) a.det = (PadicInt.Coe.ringHom (p := q)) 1
      rw [RingHom.map_det, map_one]
      exact g.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem integralSL3_mulVec_integral (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (x : Fin 3 → Padic q) (hx : ∀ i, ‖x i‖ ≤ 1) : ∀ i, ‖(g.val *ᵥ x) i‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := hg
  let y : Fin 3 → PadicInt q := fun i => ⟨x i, hx i⟩
  intro i
  have he := RingHom.map_mulVec (PadicInt.Coe.ringHom (p := q)) a.val y i
  exact (congrArg (fun z : Padic q => ‖z‖ ≤ 1) he) ▸ (a.val.mulVec y i).property

theorem integralSL3_iff_preserves_vectors (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ↔
      ∀ x : Fin 3 → Padic q, (∀ i, ‖x i‖ ≤ 1) → ∀ i, ‖(g.val *ᵥ x) i‖ ≤ 1 := by
  constructor
  · exact integralSL3_mulVec_integral q g
  · intro hg
    apply (integralSL3_iff_entries q g).mpr
    intro i j
    have hx : ∀ k, ‖(Pi.single j (1 : Padic q) : Fin 3 → Padic q) k‖ ≤ 1 := by
      intro k
      by_cases h : k = j
      · subst k
        simp
      · simp [Pi.single_eq_of_ne h]
    have h := hg (Pi.single j 1) hx i
    simpa [Matrix.mulVec_single] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates.TestTransport
