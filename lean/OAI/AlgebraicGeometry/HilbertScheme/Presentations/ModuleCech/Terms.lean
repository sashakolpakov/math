import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.BoundedComplex

/-! # Terms -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

noncomputable section

/-! Homogeneous Čech terms as finite products of actual localized degree pieces. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

def moduleCechTerm (d : ℤ) (q : ℕ) : Submodule R (Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) where
  carrier := {f | Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f ∧ Card.ProjectiveCech.ModuleCechCardSupported R M q f}
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    exact ⟨fun s => Submodule.add_mem _ (hf s) (hg s), fun s hs => by simp [hfc s hs, hgc s hs]⟩
  smul_mem' := by
    rintro r f ⟨hf, hfc⟩
    exact ⟨fun s => Submodule.smul_mem _ r (hf s), fun s hs => by simp [hfc s hs]⟩

def moduleCechTermEquiv (d : ℤ) (q : ℕ) :
    moduleCechTerm (σ := σ) R M ℳ d q ≃ₗ[R]
      ((s : {s : Finset σ // s.card = q}) → Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s.val d) where
  toFun f s := ⟨f.val s.val, f.property.1 s.val⟩
  invFun x := ⟨fun s => if hs : s.card = q then (x ⟨s, hs⟩).val else 0, by
    constructor
    · intro s
      change (if hs : s.card = q then (x ⟨s, hs⟩).val else 0) ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d
      split_ifs with hs
      · exact (x ⟨s, hs⟩).property
      · exact Submodule.zero_mem _
    · intro s hs
      exact dite_eq_right hs⟩
  left_inv f := by
    apply Subtype.ext
    funext s
    by_cases hs : s.card = q
    · simp only [dite_eq_left hs]
    · simp only [dite_eq_right hs, f.property.2 s hs]
  right_inv x := by
    funext s
    apply Subtype.ext
    simp only [dite_eq_left s.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LinearOrder σ] in
theorem moduleCechTerm_flat [Fintype σ] (d : ℤ) (q : ℕ) (hq : 0 < q)
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d)) :
    Module.Flat R (moduleCechTerm (σ := σ) R M ℳ d q) := by
  let : ∀ s : {s : Finset σ // s.card = q}, Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s.val d) :=
    fun s => hflat s.val (Finset.card_pos.mp (s.property.symm ▸ hq))
  exact Module.Flat.of_linearEquiv ((moduleCechTermEquiv (σ := σ) R M ℳ d q).trans
    (DFinsupp.linearEquivFunOnFintype (R := R)
      (M := fun s : {s : Finset σ // s.card = q} => Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s.val d)).symm)

variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleCechTermDifferential (d : ℤ) (q : ℕ) :
    moduleCechTerm (σ := σ) R M ℳ d q →ₗ[R] moduleCechTerm (σ := σ) R M ℳ d (q + 1) :=
  ((Card.ProjectiveCech.moduleCechDifferential R M).comp (moduleCechTerm (σ := σ) R M ℳ d q).subtype).codRestrict
    (moduleCechTerm (σ := σ) R M ℳ d (q + 1)) (fun f =>
      ⟨Card.ProjectiveCech.moduleCechDifferential_homogeneous R M ℳ d f.val f.property.1,
        Card.ProjectiveCech.moduleCechDifferential_card R M q f.val f.property.2⟩)

theorem moduleCechTermDifferential_square (d : ℤ) (q : ℕ) (f : moduleCechTerm (σ := σ) R M ℳ d q) :
    moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1) (moduleCechTermDifferential (σ := σ) R M ℳ d q f) = 0 := by
  apply Subtype.ext
  exact Square.ProjectiveCech.moduleCechDifferential_square R M f.val

theorem moduleCechTermDifferential_zero [Fintype σ] (d : ℤ) (q : ℕ) (hq : Fintype.card σ < q + 1) :
    moduleCechTermDifferential (σ := σ) R M ℳ d q = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact Card.ProjectiveCech.moduleCech_bounded R M (q + 1) hq _
    (Card.ProjectiveCech.moduleCechDifferential_card R M q f.val f.property.2)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech
