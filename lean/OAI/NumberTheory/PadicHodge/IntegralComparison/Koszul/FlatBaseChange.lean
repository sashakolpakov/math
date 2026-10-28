import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy
import Mathlib.Algebra.Homology.Additive
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Flat Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FlatBaseChange

noncomputable section

/-! The actual exterior Koszul complex commutes with flat scalar extension.
The comparison carries the basis wedge to its scalar-extended basis wedge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

abbrev tensorFunctor := AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S

variable (V : Type u) [AddCommGroup V] [Module R V] (s : Module.Dual R V)
  [Module.Flat R S]

def iso : ((tensorFunctor R S).mapHomologicalComplex (.down ℕ)).obj (Exterior.KoszulComplex.complex R V s) ≅
    Exterior.KoszulComplex.complex S (S ⊗[R] V) (Exterior.ContractionBaseChange.coefficient R S V s) :=
  Hom.isoOfComponents (fun n => (Exterior.ContractionBaseChange.power R S V n).toModuleIso) (by
    intro i j hij
    have hi : j + 1 = i := hij
    subst i
    dsimp only [Functor.mapHomologicalComplex_obj_d]
    rw [Exterior.KoszulHomotopy.complex_d, Exterior.KoszulHomotopy.complex_d]
    exact ModuleCat.hom_ext (Exterior.ContractionBaseChange.contraction_comp R S V s j))

theorem iso_top_generator {n : ℕ} (b : Module.Basis (Fin n) R V) :
    (iso R S V s).hom.f n (1 ⊗ₜ[R] TopExteriorCoordinates.generator b) =
      TopExteriorCoordinates.generator (b.baseChange S) := by
  change Exterior.ContractionBaseChange.power R S V n (1 ⊗ₜ[R] exteriorPower.ιMulti R n b) = _
  rw [GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv_tmul_ιMulti, one_smul]
  congr 1
  funext i
  exact (Module.Basis.baseChange_apply S b i).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FlatBaseChange
