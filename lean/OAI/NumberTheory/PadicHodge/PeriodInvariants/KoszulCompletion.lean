import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCompletion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexExtension
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionLinearDensity
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap

/-! # Koszul Completion -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion

noncomputable section

/-! # Completion of a finite Koszul complex is the Koszul complex of completed coefficients -/

open _root_.CategoryTheory

universe u
variable {R M σ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype σ] [LinearOrder σ] (I : Ideal R) (hI : I.FG)
  (D : σ → Module.End R M) (hD : ∀ i j, Function.Commute (D i) (D j))

def operator (i : σ) : Module.End R (AdicCompletion I M) := AdicCompletionLinear.map I (D i)

include hD in
omit [Fintype σ] [LinearOrder σ] in
theorem commute (i j : σ) : Function.Commute (operator I D i) (operator I D j) := by
  intro x
  have h : (D i).comp (D j) = (D j).comp (D i) := LinearMap.ext (hD i j)
  change AdicCompletion.map I (D i) (AdicCompletion.map I (D j) x) =
    AdicCompletion.map I (D j) (AdicCompletion.map I (D i) x)
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply, h]

def source : CochainComplex (ModuleCat R) ℕ := AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ M D hD

def target : CochainComplex (ModuleCat R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ (AdicCompletion I M) (operator I D) (commute I D hD)

def finiteMap : source D hD ⟶ target I D hD :=
  AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap.KoszulTensorMap.map R σ M (AdicCompletion I M) D (operator I D) (AdicCompletion.of I M)
    (fun i x => (AdicCompletion.map_of I (D i) x).symm) hD (commute I D hD)

include hI in
theorem term_complete (n : ℕ) : IsAdicComplete I ((target I D hD).X n) := by
  classical
  exact FiniteTensorCompletion.tensor_complete I
    (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n) hI

def comparison : AdicCompletionContraction.complex I (source D hD) ⟶ target I D hD :=
  ComplexExtension.extension I (source D hD) (target I D hD) (finiteMap I D hD) (term_complete I hI D hD)

theorem extends_finite : ComplexIso.inclusion I (source D hD) ≫ comparison I hI D hD = finiteMap I D hD :=
  ComplexExtension.extends_finite I (source D hD) (target I D hD) (finiteMap I D hD) (term_complete I hI D hD)

theorem component_eq (n : ℕ) : ((comparison I hI D hD).f n).hom =
    (FiniteTensorCompletion.equiv I (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n)).toLinearMap := by
  classical
  have : IsAdicComplete I ((target I D hD).X n) := term_complete I hI D hD n
  apply CompletionLinearDensity.ext I hI
  intro x
  have he := congrArg (fun f : source D hD ⟶ target I D hD => (f.f n).hom x) (extends_finite I hI D hD)
  exact he.trans (FiniteTensorCompletion.equiv_of I (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n) x).symm

theorem component_bijective (n : ℕ) : Function.Bijective (((comparison I hI D hD).f n).hom) := by
  rw [component_eq]
  exact (FiniteTensorCompletion.equiv I (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n)).bijective

def complexIso : AdicCompletionContraction.complex I (source D hD) ≅ target I D hD :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.ofBijective (((comparison I hI D hD).f n).hom)
      (component_bijective I hI D hD n)).toModuleIso)
    (fun i j _ => (comparison I hI D hD).comm i j)

theorem complexIso_hom : (complexIso I hI D hD).hom = comparison I hI D hD := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.KoszulCompletion
