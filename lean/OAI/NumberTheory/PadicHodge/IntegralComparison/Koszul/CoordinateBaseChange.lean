import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFlatBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology

/-! # Coordinate Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoordinateBaseChange

noncomputable section

/-! The canonical flat scalar-extension comparison for the Koszul complex
on a fixed finite list of equations, with its original ordered coordinates. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix

def linearIso (V W : Type u) [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (s : Module.Dual R V) (t : Module.Dual R W)
    (e : V ≃ₗ[R] W) (he : t.comp e.toLinearMap = s) :
    Exterior.KoszulComplex.complex R V s ≅ Exterior.KoszulComplex.complex R W t where
  hom := Exterior.KoszulComplex.map R V W s t e.toLinearMap he
  inv := Exterior.KoszulComplex.map R W V t s e.symm.toLinearMap (by
    ext x
    have h := LinearMap.congr_fun he (e.symm x)
    simpa using h.symm)
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ModuleCat.hom_ext
    change (exteriorPower.map n e.symm.toLinearMap).comp
      (exteriorPower.map n e.toLinearMap) = LinearMap.id
    rw [← exteriorPower.map_comp]
    simp
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ModuleCat.hom_ext
    change (exteriorPower.map n e.toLinearMap).comp
      (exteriorPower.map n e.symm.toLinearMap) = LinearMap.id
    rw [← exteriorPower.map_comp]
    simp

def coordinate (n : ℕ) : S ⊗[R] (Fin n → R) ≃ₗ[S] (Fin n → S) :=
  ((Pi.basisFun R (Fin n)).baseChange S).equivFun

theorem coordinate_tmul {n : ℕ} (a : S) (v : Fin n → R) (i : Fin n) :
    coordinate R S n (a ⊗ₜ[R] v) i = a * algebraMap R S (v i) := by
  change ((Pi.basisFun R (Fin n)).baseChange S).repr (a ⊗ₜ[R] v) i = _
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def, mul_comm]

theorem equation_coordinate {n : ℕ} (s : Fin n → R) :
    (GeneratorMatrix.equation S (algebraMap R S ∘ s)).comp (coordinate R S n).toLinearMap =
      Exterior.ContractionBaseChange.coefficient R S (Fin n → R) (GeneratorMatrix.equation R s) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, GeneratorMatrix.equation_apply,
    coordinate_tmul, Exterior.ContractionBaseChange.coefficient_tmul, Function.comp_apply, map_sum, map_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def coordinateKoszulIso {n : ℕ} (s : Fin n → R) :
    Exterior.KoszulComplex.complex S (S ⊗[R] (Fin n → R)) (Exterior.ContractionBaseChange.coefficient R S _ (GeneratorMatrix.equation R s)) ≅
      OrientedTopCohomology.koszul S (algebraMap R S ∘ s) :=
  linearIso S _ _ _ _ (coordinate R S n) (equation_coordinate R S s)

theorem coordinateKoszulIso_generator {n : ℕ} (s : Fin n → R) :
    (coordinateKoszulIso R S s).hom.f n
        (TopExteriorCoordinates.generator ((Pi.basisFun R (Fin n)).baseChange S)) =
      TopExteriorCoordinates.generator (Pi.basisFun S (Fin n)) := by
  change exteriorPower.map n (coordinate R S n).toLinearMap
    (exteriorPower.ιMulti S n _) = exteriorPower.ιMulti S n _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  change coordinate R S n (((Pi.basisFun R (Fin n)).baseChange S) i) = _
  rw [Module.Basis.baseChange_apply]
  ext j
  rw [coordinate_tmul]
  simp [Pi.basisFun_apply, Pi.single_apply]

variable [Module.Flat R S]

def iso {n : ℕ} (s : Fin n → R) :
    ((FlatBaseChange.tensorFunctor R S).mapHomologicalComplex (.down ℕ)).obj
        (OrientedTopCohomology.koszul R s) ≅
      OrientedTopCohomology.koszul S (algebraMap R S ∘ s) :=
  FlatBaseChange.iso R S _ (GeneratorMatrix.equation R s) ≪≫ coordinateKoszulIso R S s

theorem iso_top_generator {n : ℕ} (s : Fin n → R) :
    (iso R S s).hom.f n
        (1 ⊗ₜ[R] TopExteriorCoordinates.generator (Pi.basisFun R (Fin n))) =
      TopExteriorCoordinates.generator (Pi.basisFun S (Fin n)) := by
  change (coordinateKoszulIso R S s).hom.f n
    ((FlatBaseChange.iso R S _ (GeneratorMatrix.equation R s)).hom.f n _) = _
  rw [FlatBaseChange.iso_top_generator, coordinateKoszulIso_generator]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoordinateBaseChange
