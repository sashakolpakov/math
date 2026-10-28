import OAI.RepresentationTheory.Weil.AdelicSplitting.GraphReduction

/-! # Compatibility Reduction -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CompatibilityReduction.Construction

noncomputable section

/-! Extension of the rational operator comparison from the two open cells.
No comparison identity is assumed in the definition of the locus below. -/

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def rationalUnitaryGraphMap : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val →*
    Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) × Vacuum.Construction.GlobalCover F (n * m) C.ψ :=
  (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational).prod
    ((Assembly.Construction.constructedAdelicLift F d n m H K hd C P D).toMonoidHom.comp
      (Integral.Construction.rationalPair F H.val K.val))

def rationalCompatibilityLocus : Subgroup (UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :=
  (Rational.Construction.rationalGraph F (n * m) C.ψ).comap (rationalUnitaryGraphMap F d hd n m H K C P D)

theorem rationalCompatibilityLocus_eq_top_of_open_cells (hns : ¬ IsSquare d)
    (hH : ∀ g : UnitaryBase.Construction.Unitary H.val, IsUnit (g.val.val - 1) →
      (g, 1) ∈ rationalCompatibilityLocus F d hd n m H K C P D)
    (hK : ∀ g : UnitaryBase.Construction.Unitary K.val, IsUnit (g.val.val - 1) →
      (1, g) ∈ rationalCompatibilityLocus F d hd n m H K C P D) :
    rationalCompatibilityLocus F d hd n m H K C P D = ⊤ := by
  let R := rationalCompatibilityLocus F d hd n m H K C P D
  have h₁ (g : UnitaryBase.Construction.Unitary H.val) : (g, 1) ∈ R := by
    obtain ⟨a, b, rfl, ha, hb⟩ := UnitaryAlgebra.Construction.rational_unitary_open_factorization d hns H.val g
    have h := R.mul_mem (hH a ha) (hH b hb)
    simpa only [Prod.mk_mul_mk, one_mul] using h
  have h₂ (g : UnitaryBase.Construction.Unitary K.val) : (1, g) ∈ R := by
    obtain ⟨a, b, rfl, ha, hb⟩ := UnitaryAlgebra.Construction.rational_unitary_open_factorization d hns K.val g
    have h := R.mul_mem (hK a ha) (hK b hb)
    simpa only [Prod.mk_mul_mk, one_mul] using h
  apply top_unique
  intro g _
  have h := R.mul_mem (h₁ g.1) (h₂ g.2)
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta] using h

theorem rational_compatibility_of_graph_and_open_cells (hns : ¬ IsSquare d)
    (r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ)
    (hr : ∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a)
    (hH : ∀ g : UnitaryBase.Construction.Unitary H.val, IsUnit (g.val.val - 1) →
      (g, 1) ∈ rationalCompatibilityLocus F d hd n m H K C P D)
    (hK : ∀ g : UnitaryBase.Construction.Unitary K.val, IsUnit (g.val.val - 1) →
      (1, g) ∈ rationalCompatibilityLocus F d hd n m H K C P D)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) =
      r (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g) := by
  have ht := rationalCompatibilityLocus_eq_top_of_open_cells F d hd n m H K C P D hns hH hK
  have hg : g ∈ rationalCompatibilityLocus F d hd n m H K C P D := by rw [ht]; trivial
  exact ((hr _ _).mp hg).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CompatibilityReduction.Construction
