import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential

/-! # Edges -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Edges

noncomputable section

/-! The two boundary cases of the genuine mixed Koszul fraction map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
variable (R : Type u) [CommRing R]

theorem contraction_zero_degree (V : Type u) [AddCommGroup V] [Module R V]
    (l : Module.Dual R V) (x : ⋀[R]^0 V) : AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l x.val = 0 := by
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 0 : (Fin 0 → V) → ⋀[R]^0 V)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      change AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V l (ExteriorAlgebra.ιMulti R 0 v) = 0
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact CliffordAlgebra.contractLeft_one 0 l
  | zero => simp
  | add y z _ _ hy hz => simp only [Submodule.coe_add, map_add, hy, hz, add_zero]
  | smul a y _ hy => simp only [Submodule.coe_smul_of_tower, map_smul, hy, smul_zero]

variable {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

theorem insertion_zero (p : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) 0)
    (x : ⋀[R]^p (Fractions.normal R (c := c))) :
    Differential.insertionAt R p 0 p (by omega) a x =
      exteriorPower.map p (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m))) x := by
  apply Subtype.ext
  rw [Differential.insertionAt_coe, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem left_contraction (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (x : ⋀[R]^0 (Fractions.normal R (c := c))) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) q (Differential.insertionAt R 0 (q + 1) (q + 1) (by omega) a x) =
      ∑ k : Fin (q + 1), ((-1 : R) ^ k.val * t (a.val k).down) •
        Differential.insertionAt R 0 q q (by omega) (a.delete k) x := by
  apply Subtype.ext
  simp only [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_coe, Differential.insertionAt_coe, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Contraction.homogeneous_mul, contraction_zero_degree,
    zero_mul, pow_zero, one_smul, zero_add, Koszul.CechEvaluation.ambient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Differential.equation_tuple, mul_smul_comm]
  rfl

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem right (p : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) 0)
    (φ : Module.Dual R (⋀[R]^p (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^(p + 1) (Fractions.normal R (c := c))) :
    CechDifferential.value R P U t ht (p + 1) 0 (p + 1) (by omega) a
      (φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) p)) x =
    CechDifferential.value R P U t ht p 0 p (by omega) a φ
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x) := by
  simp only [CechDifferential.value, LinearMap.comp_apply, insertion_zero]
  exact congrArg (fun z => Fractions.reciprocal R P U t ht a * algebraMap R _ (φ z))
    (LinearMap.congr_fun (Exterior.KoszulComplex.contraction_naturality R
      (Fractions.normal R (c := c)) (Fractions.ambient R (c := c) (m := m))
      (Koszul.GeneratorMatrix.equation R s) (Differential.equation R s t)
      (LinearMap.inl R _ _) (Differential.equation_inl R s t) p) x)

private theorem cancel_product {A : Type*} [CommRing A] (d v t z e z' : A)
    (hc : t * d = e) (hz : z' = z) : d * (v * t * z) = v * (e * z') := by
  rw [hz, ← hc]
  ring

theorem left (q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (φ : Module.Dual R (⋀[R]^q (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^0 (Fractions.normal R (c := c))) :
    CechDifferential.value R P U t ht 0 (q + 1) (q + 1) (by omega) a
      (φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) q)) x =
      ∑ k : Fin (q + 1), (-1 : R) ^ k.val •
        (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom
          (CechDifferential.value R P U t ht 0 q q (by omega) (a.delete k) φ x) := by
  simp only [CechDifferential.value, LinearMap.comp_apply]
  rw [left_contraction, map_sum]
  simp only [map_smul, smul_eq_mul, Algebra.smul_def, map_mul, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hα := (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom.commutes
    (φ (Differential.insertionAt R 0 q q (by omega) (a.delete k) x))
  exact cancel_product _ _ _ _ _ _ (CechDifferential.cancel R P U t ht a k) hα

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Edges
