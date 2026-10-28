import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension
import OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing

/-! # Thickening Cohomology Bound -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ThickeningCohomologyBound

noncomputable section

/-! The relative dimension of a smooth scheme over a perfect field
bounds the sheaf cohomology of every Noetherian closed thickening.
The bound uses the actual underlying topological spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {k : Type u} [Field k] [PerfectField k]
  (X : Over (Spec (CommRingCat.of k))) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

theorem dimension_le : topologicalKrullDim X.left ≤ (g : WithBot ℕ∞) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_specialization_krullDim, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro z
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints
    (Z := closure ({z} : Set X.left)) (Set.singleton_nonempty z).closure
    isClosed_closure.isLocallyClosed
  have hyz : y ≤ z := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
  have hle : (Order.coheight z : WithBot ℕ∞) ≤ (Order.coheight y : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr (Order.coheight_anti hyz)
  have hyDim : (Order.coheight y : WithBot ℕ∞) = (g : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    exact ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension g X.hom y hyc
  exact hle.trans_eq hyDim

variable {Y : Scheme.{u}} (i : X.left ⟶ Y) [IsClosedImmersion i] [Surjective i]

include X i in
theorem thickening_dimension_le : topologicalKrullDim Y ≤ (g : WithBot ℕ∞) := by
  rw [← ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction.topologicalKrullDim_eq_of_integral_surjective i]
  exact dimension_le X g

include X i in
theorem cohomology [NoetherianSpace Y] (n : ℕ) (hn : g < n)
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y.toTopCat) :
    Subsingleton (CategoryTheory.Sheaf.H F n) := by
  let : NoetherianSpace Y.toTopCat := inferInstanceAs (NoetherianSpace Y)
  apply OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing.Projective.GrothendieckVanishing Y.toTopCat n _ F
  exact lt_of_le_of_lt (thickening_dimension_le X g i) (by exact_mod_cast hn)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ThickeningCohomologyBound
