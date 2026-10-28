import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Singular Coefficient Exact -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientExact

noncomputable section

/-! Pointwise exactness of actual singular cochains in the coefficient module. -/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

variable {R : Type} [Ring R] {M N P : ModuleCat.{0} R}
  (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0})

theorem coefficientCochain_injective (hf : Function.Injective f) (n : ℕ) :
    Function.Injective ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n) := by
  intro a b hab
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).hom a = (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).hom b
  ext s
  apply hf
  have h := congrArg (fun c => (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso N X n).hom c s) hab
  exact (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply f X a s).symm.trans
    (h.trans (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply f X b s))

theorem coefficientCochain_lift (n : ℕ) (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X n)
    (hb : ∀ s, ∃ a : M, f a = (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso N X n).hom b s) :
    ∃ a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n, (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a = b := by
  let a := (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).inv (fun s => (hb s).choose)
  refine ⟨a, ?_⟩
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso N X n).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso N X n).hom ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a) =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso N X n).hom b
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply f X a s]
  change f ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).hom
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n).inv (fun s => (hb s).choose)) s) = _
  rw [Iso.inv_hom_id_apply]
  exact (hb s).choose_spec

theorem coefficientCochain_surjective (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n) :=
  fun b => coefficientCochain_lift f X n b (fun _ => hf _)

theorem coefficientCochain_exact
    (he : ∀ b : N, g b = 0 ↔ ∃ a : M, f a = b)
    (n : ℕ) (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).X n)
    (hb : (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f n b = 0) :
    ∃ a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n, (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a = b := by
  apply coefficientCochain_lift f X n b
  intro s
  apply (he _).mp
  have h := congrArg (fun c => (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom c s) hb
  have hz : (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom 0 s = 0 :=
    congrFun (map_zero (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom.hom) s
  exact (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply g X b s).symm.trans (h.trans hz)

theorem coefficientCochain_comp_zero (hz : ∀ a : M, g (f a) = 0)
    (n : ℕ) (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f n ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a) = 0 := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).toLinearEquiv.injective
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f n ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a)) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom 0
  ext s
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply g X ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a) s,
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_apply f X a s]
  exact (hz _).trans (congrFun (map_zero (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso P X n).hom.hom) s).symm

theorem coefficientCochain_d (n : ℕ) (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d n (n + 1) ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f n a) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f (n + 1) ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d n (n + 1) a) :=
  ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).comm n (n + 1)) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientExact
