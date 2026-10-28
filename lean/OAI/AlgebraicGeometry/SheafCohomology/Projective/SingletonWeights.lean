import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData

/-! # Singleton Weights -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

/-! Homogeneous weights and cochains for projective space with a single coordinate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
open _root_.MvPolynomial
variable {σ : Type}

theorem LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.subsingleton_of_subsingleton [Subsingleton σ] (d : ℤ) :
    Subsingleton (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) := by
  have value (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) (i : σ) : e.1 i = d := by
    have he : e.1 = Finsupp.single i (e.1 i) :=
      Finsupp.eq_single_iff.mpr ⟨fun k _ => by simp [Subsingleton.elim k i], rfl⟩
    have hd := e.2
    rw [he, Finsupp.degree_single] at hd
    exact hd
  constructor
  intro e f
  apply Subtype.ext
  ext i
  rw [value e i, value f i]

theorem SingletonWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject_module_finite_of_subsingleton
    {R : Type u} [CommRing R] [Fintype σ] [LinearOrder σ] [Subsingleton σ]
    (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) := by
  let := LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.subsingleton_of_subsingleton (σ := σ) d
  let A := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let F := fun a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.of A (AddMonoidAlgebra A
      {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e.IsAllowedOn (fun k => (a.1 k).down)})
  have : ∀ a, Module.Finite A (F a) := fun _ => inferInstance
  let : Finite (OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) := by
    unfold OrderedBaseCech.Scheme.Modules.OrderedCechIndex
    infer_instance
  let : Module.Finite A (∀ a, F a) := Module.Finite.pi
  exact Module.Finite.equiv (ModuleCat.piIsoPi F).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
