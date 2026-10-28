import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.ObjectExt

/-! # Empty Etale Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyEtaleCohomology

noncomputable section

/-! All original rational pro-étale cohomology groups of an empty scheme vanish. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsEmpty X]

theorem presheaf : IsZero (Cohomology.rationalCoefficientSheaf ℓ X).obj := by
  rw [Functor.isZero_iff]
  intro U
  let : IsEmpty U.unop.left := ⟨fun x => @IsEmpty.false X inferInstance (U.unop.hom x)⟩
  change IsZero (ModuleCat.of (Cohomology.Coeff.{u} ℓ) C(U.unop.left, Cohomology.Coeff.{u} ℓ))
  exact ModuleCat.isZero_of_subsingleton _

theorem sheaf : IsZero (Cohomology.rationalCoefficientSheaf ℓ X) :=
  (Sheaf.isTerminalOfEqTop (Scheme.ProEt.topology_eq_top_of_isEmpty X) _).isZero

theorem cohomology (n : ℕ) : Subsingleton (Cohomology.RationalEllAdicCohomology ℓ X n) :=
  Zero.ObjectExt.target (Cohomology.constantUnitSheaf ℓ X)
    (Cohomology.rationalCoefficientSheaf ℓ X) n (sheaf ℓ X)

theorem finite (n : ℕ) : FiniteDimensional ℚ_[ℓ] (Cohomology.RationalEllAdicCohomology ℓ X n) := by
  let := cohomology ℓ X n
  infer_instance

theorem charpoly (n : ℕ) (f : Module.End ℚ_[ℓ] (Cohomology.RationalEllAdicCohomology ℓ X n)) :
    letI := finite ℓ X n
    f.charpoly = 1 := by
  let := cohomology ℓ X n
  have hf : f = 0 := Subsingleton.elim _ _
  rw [hf, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyEtaleCohomology
