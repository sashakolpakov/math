import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate

/-! # De Rham Tensor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor

noncomputable section

/-!
# The coordinate differential agrees with the actual PD differential

Expanding the universal PD derivation in coordinate one-forms expands
the first slot of every differential symbol. This identifies the tensor
coordinate complex with the actual PD de Rham complex.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor.PDFormsTensor

universe u

variable (R A σ : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I) (x : σ → A) [Fintype σ]
  (D : σ → Module.End R A)
  (hD : ∀ a, OneForms.PDOneForms.D R A I δ a = ∑ i, D i a • OneForms.PDOneForms.D R A I δ (x i))

include hD in
theorem symbol_cons_expansion (n : ℕ) (a : A) (v : Fin n → A) :
    DeRham.PDDeRham.symbol R A I δ 1 (Fin.cons a v) =
      ∑ i, D i a • DeRham.PDDeRham.symbol R A I δ 1 (Fin.cons (x i) v) := by
  let L := OneForms.PDOneForms.lift R A I δ (DeRham.PDDeRham.Form R A I δ (n + 1))
    (FormSlots.PDFormSlots.derivation R A I δ (Fin.cons a v) 0)
    (fun m _ ha => FormSlots.PDFormSlots.derivation_dpow R A I δ (Fin.cons a v) 0 m ha)
  have he := congrArg L (hD a)
  simpa only [L, map_sum, map_smul, OneForms.PDOneForms.lift_D,
    FormSlots.PDFormSlots.derivation_apply, Fin.update_cons_zero] using he

theorem differential_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    DeRham.PDDeRham.differential R A I δ n (DeRham.PDDeRham.symbol R A I δ a v) =
      DeRham.PDDeRham.symbol R A I δ 1 (Fin.cons a v) :=
  DeRham.PDDeRham.projectedDifferential_symbol R A I δ a v

omit [Fintype σ] in
theorem toForms_wedge_word (n : ℕ) (a : A) (i : σ) (v : Fin n → σ) :
    FormsTensor.PDFormsTensor.toForms R A σ I δ x (n + 1)
      (a ⊗ₜ[R] Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n
        (exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1))) =
          DeRham.PDDeRham.symbol R A I δ a (Fin.cons (x i) (x ∘ v)) := by
  rw [Koszul.Tensor.KoszulTensor.exteriorWedge, ExteriorContractionCoe.ExteriorContraction.wedge_ιMulti]
  have hv : Fin.cons (Finsupp.single i (1 : R)) (fun k => Finsupp.single (v k) 1) =
      (fun k : Fin (n + 1) => Finsupp.single ((Fin.cons i v : Fin (n + 1) → σ) k) (1 : R)) := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  rw [hv, FormsTensor.PDFormsTensor.toForms_word]
  congr 1
  funext k
  exact Fin.cases rfl (fun _ => rfl) k

include hD in
theorem differential_compatibility (n : ℕ) :
    ((FormsTensor.PDFormsTensor.toForms R A σ I δ x (n + 1)).restrictScalars R).comp (Koszul.Tensor.KoszulTensor.differential R σ A D n) =
      (DeRham.PDDeRham.differential R A I δ n).comp ((FormsTensor.PDFormsTensor.toForms R A σ I δ x n).restrictScalars R) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext_on (ExteriorCoordinate.ExteriorCoordinateProjection.word_span R σ n)
  rintro _ ⟨v, rfl⟩
  change FormsTensor.PDFormsTensor.toForms R A σ I δ x (n + 1)
    (Koszul.Tensor.KoszulTensor.differential R σ A D n (a ⊗ₜ[R] exteriorPower.ιMulti R n
      (fun k => Finsupp.single (v k) 1))) =
        DeRham.PDDeRham.differential R A I δ n
          (FormsTensor.PDFormsTensor.toForms R A σ I δ x n (a ⊗ₜ[R] exteriorPower.ιMulti R n
            (fun k => Finsupp.single (v k) 1)))
  rw [Koszul.Tensor.KoszulTensor.differential_tmul, map_sum, FormsTensor.PDFormsTensor.toForms_word, differential_symbol,
    symbol_cons_expansion R A σ I δ x D hD]
  apply Finset.sum_congr rfl
  intro i _
  rw [toForms_wedge_word, DeRham.PDDeRham.symbol_smul_one]

variable [LinearOrder σ] (b : Module.Basis σ A (DeRham.PDDeRham.Form R A I δ 1))
  (hb : ∀ i, b i = OneForms.PDOneForms.D R A I δ (x i))
  (hcomm : ∀ i j, Function.Commute (D i) (D j))

local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.complex R σ A D hcomm
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ

def complexIso : T ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (FormsTensor.PDFormsTensor.formsEquiv R A σ I δ x b hb n).restrictScalars R |>.toModuleIso)
    (by
      intro n m hnm
      have hm : n + 1 = m := hnm
      subst m
      dsimp only [Koszul.Tensor.KoszulTensor.complex, DeRham.PDDeRham.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (differential_compatibility R A σ I δ x D hD n).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor.PDDeRhamTensor
