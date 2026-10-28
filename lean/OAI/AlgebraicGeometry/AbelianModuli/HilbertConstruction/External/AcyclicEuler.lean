import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionDimensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Acyclic Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicEuler

noncomputable section

/-! Euler characteristics multiply for external tensor products of line
bundles with no positive cohomology. Both vanishing and the degree-zero
dimension comparison refer to the actual sheaf cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficientEulerCharacteristic_eq_finrank_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules)
    (hM : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H M (q + 1))) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic f M =
      (Module.finrank k ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) 0).obj M) : ℤ) := by
  unfold CohomologyEulerCharacteristic.coefficientEulerCharacteristic
  rw [finsum_eq_single _ 0]
  · simp
  · intro q hq
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    let : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap f) (r + 1)).obj M) := hM r
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

include H V hV haV heV haU heU in
theorem fieldExternal_euler_of_positive_vanishing (hU : iSup U = ⊤)
    (hL : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf (q + 1)))
    (hN : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N.sheaf (q + 1))) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (b ≫ g) (((L.pullback a).tensor (N.pullback b)).sheaf) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic f L.sheaf * CohomologyEulerCharacteristic.coefficientEulerCharacteristic g N.sheaf := by
  have hE := AcyclicTensor.fieldExternal_positiveCohomology_vanish H L N V hV haV heV U haU heU hU hL hN
  rw [coefficientEulerCharacteristic_eq_finrank_zero (b ≫ g) _ hE,
    coefficientEulerCharacteristic_eq_finrank_zero f L.sheaf hL,
    coefficientEulerCharacteristic_eq_finrank_zero g N.sheaf hN]
  exact_mod_cast SectionDimensions.fieldExternalZeroCohomology_finrank H L N V hV haV heV U haU heU hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicEuler
