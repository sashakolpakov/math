import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal

/-! # Place At -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask

/-! Split actual adelic quadratic coefficients into a finite set of
places and a complementary half-integral matrix. -/

open scoped Classical _root_.Matrix
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM

def mask (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  ⟨fun v => if v ∈ S then a v else 0, by
    filter_upwards [a.property] with v hv
    split_ifs
    · exact hv
    · exact (v.adicCompletionIntegers ℚ).zero_mem⟩

theorem mask_eval (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    mask S a v = if v ∈ S then a v else 0 := rfl

theorem mask_add_compl (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : mask S a + mask Sᶜ a = a := by
  apply DFunLike.ext
  intro v
  change SymplecticLocal.CM.localEval v (mask S a + mask Sᶜ a) = a v
  rw [map_add]
  change mask S a v + mask Sᶜ a v = a v
  rw [mask_eval, mask_eval]
  by_cases hv : v ∈ S <;> simp [hv]

variable {I : Type*} [Fintype I]

def matrixMask (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := fun i j => mask S (B i j)

omit [Fintype I] in
theorem matrixMask_symmetric (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    (matrixMask S B).IsSymm := by
  apply Matrix.ext
  intro i j
  change mask S (B j i) = mask S (B i j)
  exact congrArg (mask S) (hB.apply i j)

omit [Fintype I] in
theorem matrixMask_add_compl (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    matrixMask S B + matrixMask Sᶜ B = B := by
  apply Matrix.ext
  intro i j
  exact mask_add_compl S (B i j)

theorem exists_halfIntegral_complement (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, IntegralVacuum.CM.HalfIntegral (matrixMask (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace)ᶜ B) := by
  have he : ∀ᶠ v in cofinite, ∀ i j,
      (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j).property
  have hbad : {v | ¬∀ i j, (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ}.Finite := he
  refine ⟨hbad.toFinset, ?_⟩
  intro i j v
  change (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2)) v * (mask (hbad.toFinset : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace)ᶜ (B i j)) v ∈ _
  rw [mask_eval]
  simp only [Set.mem_compl_iff, Finset.mem_coe]
  by_cases hv : v ∈ hbad.toFinset
  · rw [ite_eq_right (not_not.mpr hv), mul_zero]
    exact (v.adicCompletionIntegers ℚ).zero_mem
  · have hg : ∀ i j, (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
    rw [ite_eq_left hv]
    exact hg i j

def SupportedAt (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  ∀ i v, v ∉ S → x i v = 0

def MatrixAway (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Prop :=
  ∀ i j v, v ∈ S → B i j v = 0

omit [Fintype I] in
theorem matrixMask_compl_away (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    MatrixAway S (matrixMask Sᶜ B) := by
  intro i j v hv
  change mask Sᶜ (B i j) v = 0
  simp [mask_eval, hv]

theorem mulVec_zero_of_disjoint (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : MatrixAway S B) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hx : SupportedAt S x) : B *ᵥ x = 0 := by
  funext i
  apply DFunLike.ext
  intro v
  change SymplecticLocal.CM.localEval v (∑ j, B i j * x j) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_mul]
  change B i j v * x j v = 0
  by_cases hv : v ∈ S
  · rw [hB i j v hv, zero_mul]
  · rw [hx j v hv, mul_zero]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.CyclicVacuum

/-! Operators fixing the vacuum and a family of Heisenberg phases fix
the entire corresponding cyclic subspace. Away integral generators
therefore act identically on every finite-place cyclic subspace. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask
variable {I : Type*} [Fintype I]

theorem action_heisenberg_of_fixed (g : FiniteOscillator.CM.Oscillator (I := I)) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hp : FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection g) (Sum.elim p q) = Sum.elim p q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : FiniteOscillator.CM.action g (FourierHeisenberg.CM.operator p q f) = FourierHeisenberg.CM.operator p q (FiniteOscillator.CM.action g f) := by
  have hh : FiniteOscillator.CM.graph (Sum.elim p q) f (FourierHeisenberg.CM.operator p q f) := rfl
  have h := (g.property.2 (Sum.elim p q) f (FourierHeisenberg.CM.operator p q f)).mp hh
  change FiniteOscillator.CM.graph (FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection g) (Sum.elim p q)) (FiniteOscillator.CM.action g f)
    (FiniteOscillator.CM.action g (FourierHeisenberg.CM.operator p q f)) at h
  rw [hp] at h
  exact Subtype.ext h

def cyclicSpace (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Submodule ℂ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :=
  Submodule.span ℂ {f | ∃ p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Mask.SupportedAt S p ∧ Mask.SupportedAt S q ∧
    f = FourierHeisenberg.CM.operator p q RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction}

theorem fixes_cyclicSpace (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (g : FiniteOscillator.CM.Oscillator (I := I))
    (hg : FiniteOscillator.CM.action g RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)
    (hp : ∀ p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Mask.SupportedAt S p → Mask.SupportedAt S q →
      FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection g) (Sum.elim p q) = Sum.elim p q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hf : f ∈ cyclicSpace S) : FiniteOscillator.CM.action g f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p, q, hps, hqs, rfl⟩ := hf
    rw [action_heisenberg_of_fixed g p q (hp p q hps hqs), hg]
  | zero => exact map_zero _
  | add f h _ _ hf hh => rw [map_add, hf, hh]
  | smul c f _ hf => rw [map_smul, hf]

theorem upper_away_phase (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm)
    (ha : Mask.MatrixAway S B) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hq : Mask.SupportedAt S q) :
    FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection (Quadratic.CM.quadraticOscillator B hB)) (Sum.elim p q) = Sum.elim p q := by
  change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB).val *ᵥ Sum.elim p q = Sum.elim p q
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper_phase, Mask.mulVec_zero_of_disjoint S B ha q hq, add_zero]

theorem lower_phase (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    FiniteOscillator.CM.phaseAction (IntegralVacuum.CM.LowerBare.lower B hB) (Sum.elim p q) = Sum.elim p (B *ᵥ p + q) := by
  change Matrix.fromBlocks 1 0 B 1 *ᵥ Sum.elim p q = _
  rw [Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]

theorem lower_away_phase (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm)
    (ha : Mask.MatrixAway S B) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hp : Mask.SupportedAt S p) :
    FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection (IntegralVacuum.CM.LowerBare.lowerLift B hB).val) (Sum.elim p q) = Sum.elim p q := by
  change FiniteOscillator.CM.phaseAction (BareNe.CM.Group.bareProjection (IntegralVacuum.CM.LowerBare.lowerLift B hB)) (Sum.elim p q) = _
  rw [IntegralVacuum.CM.LowerBare.lowerLift_projection, lower_phase, Mask.mulVec_zero_of_disjoint S B ha p hp, zero_add]

theorem upper_fixes_cyclicSpace (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : B.IsSymm) (hi : IntegralVacuum.CM.HalfIntegral B) (ha : Mask.MatrixAway S B)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hf : f ∈ cyclicSpace S) :
    Quadratic.CM.finiteQuadratic B f = f :=
  fixes_cyclicSpace S (Quadratic.CM.quadraticOscillator B hB) (IntegralVacuum.CM.quadratic_vacuum B hi)
    (fun p q _ hq => upper_away_phase S B hB ha p q hq) f hf

theorem lower_fixes_cyclicSpace (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : B.IsSymm) (hi : IntegralVacuum.CM.HalfIntegral B) (ha : Mask.MatrixAway S B)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hf : f ∈ cyclicSpace S) :
    BareNe.CM.Group.bareAction (IntegralVacuum.CM.LowerBare.lowerLift B hB) f = f :=
  fixes_cyclicSpace S (IntegralVacuum.CM.LowerBare.lowerLift B hB).val (IntegralVacuum.CM.lower_vacuum B hB hi)
    (fun p q hp _ => lower_away_phase S B hB ha p q hp) f hf

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.CyclicVacuum

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.QuadraticAddition

/-! Exact additive composition of actual upper and lower quadratic
operators, including finite-place mask decompositions. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask
variable {I : Type*} [Fintype I]

theorem quadratic_add (B C : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B + C) x = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x + RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic C x := by
  simp only [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic, Matrix.add_mulVec, dotProduct_add, mul_add]

theorem operator_add (B C : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Quadratic.CM.finiteQuadratic (B + C) = Quadratic.CM.finiteQuadratic B * Quadratic.CM.finiteQuadratic C := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  funext x
  change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B + C) x) * f.val x =
    Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) *
      (Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic C x) * f.val x)
  rw [quadratic_add, AddChar.map_add_eq_mul, mul_assoc]

theorem oscillator_add (B C : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (hC : C.IsSymm) :
    Quadratic.CM.quadraticOscillator (B + C) (hB.add hC) = Quadratic.CM.quadraticOscillator B hB * Quadratic.CM.quadraticOscillator C hC := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (B + C) (hB.add hC)).val = (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB).val * (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper C hC).val
    simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, Matrix.fromBlocks_multiply, add_comm]
  · exact operator_add B C

theorem lowerLift_add (B C : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (hC : C.IsSymm) :
    IntegralVacuum.CM.LowerBare.lowerLift (B + C) (hB.add hC) = IntegralVacuum.CM.LowerBare.lowerLift B hB * IntegralVacuum.CM.LowerBare.lowerLift C hC := by
  apply Subtype.ext
  change FiniteOscillator.CM.fourierOscillator⁻¹ * Quadratic.CM.quadraticOscillator (-(B + C)) _ * FiniteOscillator.CM.fourierOscillator =
    (FiniteOscillator.CM.fourierOscillator⁻¹ * Quadratic.CM.quadraticOscillator (-B) _ * FiniteOscillator.CM.fourierOscillator) *
      (FiniteOscillator.CM.fourierOscillator⁻¹ * Quadratic.CM.quadraticOscillator (-C) _ * FiniteOscillator.CM.fourierOscillator)
  simp only [neg_add]
  rw [oscillator_add (-B) (-C) hB.neg hC.neg]
  group

theorem upper_mask_decomposition (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Quadratic.CM.quadraticOscillator B hB =
      Quadratic.CM.quadraticOscillator (Mask.matrixMask S B) (Mask.matrixMask_symmetric S B hB) *
      Quadratic.CM.quadraticOscillator (Mask.matrixMask Sᶜ B) (Mask.matrixMask_symmetric Sᶜ B hB) := by
  rw [← oscillator_add]
  congr 1
  exact (Mask.matrixMask_add_compl S B).symm

theorem lower_mask_decomposition (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    IntegralVacuum.CM.LowerBare.lowerLift B hB =
      IntegralVacuum.CM.LowerBare.lowerLift (Mask.matrixMask S B) (Mask.matrixMask_symmetric S B hB) *
      IntegralVacuum.CM.LowerBare.lowerLift (Mask.matrixMask Sᶜ B) (Mask.matrixMask_symmetric Sᶜ B hB) := by
  rw [← lowerLift_add]
  congr 1
  exact (Mask.matrixMask_add_compl S B).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.QuadraticAddition

end

end OAI
