import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal

/-! # Forms Tensor Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensorNaturality.PDFormsTensorNaturality

noncomputable section

/-! # Naturality of the actual coordinate tensor description of PD forms -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
  (δ : DividedPowers I) (ε : DividedPowers J) (x : σ → A) (y : σ → B)
  (f : A →ₐ[R] B) (hf : DividedPowers.IsDPMorphism δ ε f.toRingHom)
  (hxy : ∀ i, f (x i) = y i)

include hxy in
theorem toForms_naturality (n : ℕ) :
    (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n).comp
      ((FormsTensor.PDFormsTensor.toForms R A σ I δ x n).restrictScalars R) =
        ((FormsTensor.PDFormsTensor.toForms R B σ J ε y n).restrictScalars R).comp
          (TensorProduct.map f.toLinearMap LinearMap.id) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext_on (ExteriorCoordinate.ExteriorCoordinateProjection.word_span R σ n)
  rintro _ ⟨v, rfl⟩
  change DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n
    (FormsTensor.PDFormsTensor.toForms R A σ I δ x n (a ⊗ₜ[R]
      exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1))) =
        FormsTensor.PDFormsTensor.toForms R B σ J ε y n (f a ⊗ₜ[R]
          exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1))
  rw [FormsTensor.PDFormsTensor.toForms_word, FormsTensor.PDFormsTensor.toForms_word]
  have hs := DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (A := CommAlgCat.of R A) (B := CommAlgCat.of R B)
    (CommAlgCat.ofHom f) hf n a (x ∘ v)
  apply hs.trans
  change DeRham.PDDeRham.symbol R B J ε (f a) (fun k => f (x (v k))) = DeRham.PDDeRham.symbol R B J ε (f a) (y ∘ v)
  congr 1
  exact funext (fun k => hxy (v k))

variable [LinearOrder σ]
  (b : Module.Basis σ A (DeRham.PDDeRham.Form R A I δ 1)) (hb : ∀ i, b i = OneForms.PDOneForms.D R A I δ (x i))
  (c : Module.Basis σ B (DeRham.PDDeRham.Form R B J ε 1)) (hc : ∀ i, c i = OneForms.PDOneForms.D R B J ε (y i))

include hxy in
theorem formsEquiv_naturality (n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term R σ A n) :
    FormsTensor.PDFormsTensor.formsEquiv R B σ J ε y c hc n (TensorProduct.map f.toLinearMap LinearMap.id z) =
      DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n (FormsTensor.PDFormsTensor.formsEquiv R A σ I δ x b hb n z) :=
  (LinearMap.congr_fun (toForms_naturality R A B σ I J δ ε x y f hf hxy n) z).symm

include hxy in
theorem formsEquiv_symm_naturality (n : ℕ) (ω : DeRham.PDDeRham.Form R A I δ n) :
    (FormsTensor.PDFormsTensor.formsEquiv R B σ J ε y c hc n).symm
      (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom f) hf n ω) =
        TensorProduct.map f.toLinearMap LinearMap.id ((FormsTensor.PDFormsTensor.formsEquiv R A σ I δ x b hb n).symm ω) := by
  apply (FormsTensor.PDFormsTensor.formsEquiv R B σ J ε y c hc n).injective
  rw [LinearEquiv.apply_symm_apply, formsEquiv_naturality R A B σ I J δ ε x y f hf hxy b hb c hc,
    LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormsTensorNaturality.PDFormsTensorNaturality
