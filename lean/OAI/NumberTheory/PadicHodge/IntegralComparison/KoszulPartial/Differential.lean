import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions

/-! # Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential

noncomputable section

/-! The literal mixed Koszul differential separates into the normal
Koszul differential and the signed deleted point-parameter terms. -/
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] {c m : ℕ}

def insertionAt (p q d : ℕ) (h : p + q = d) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) :
    (⋀[R]^p (Fractions.normal R (c := c))) →ₗ[R] (⋀[R]^d (Fractions.ambient R (c := c) (m := m))) where
  toFun x := ⟨(Fractions.insertion R p q a x).val, h ▸ (Fractions.insertion R p q a x).property⟩
  map_add' x y := by
    apply Subtype.ext
    change (Fractions.insertion R p q a (x + y)).val = _
    exact congrArg (fun z : ⋀[R]^(p + q) (Fractions.ambient R (c := c) (m := m)) => z.val)
      (map_add (Fractions.insertion R p q a) x y)
  map_smul' r x := by
    apply Subtype.ext
    change (Fractions.insertion R p q a (r • x)).val = _
    exact congrArg (fun z : ⋀[R]^(p + q) (Fractions.ambient R (c := c) (m := m)) => z.val)
      (map_smul (Fractions.insertion R p q a) r x)

theorem insertionAt_coe (p q d : ℕ) (h : p + q = d) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q)
    (x : ⋀[R]^p (Fractions.normal R (c := c))) :
    (insertionAt R p q d h a x).val =
      (exteriorPower.map p (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m))) x).val *
        ExteriorAlgebra.ιMulti R q (Fractions.tuple R a) := rfl

variable (s : Fin c → R) (t : Fin m → R)

def equation : Module.Dual R (Fractions.ambient R (c := c) (m := m)) :=
  (Koszul.GeneratorMatrix.equation R s).coprod (Koszul.GeneratorMatrix.equation R t)

theorem equation_inl : (equation R s t).comp (LinearMap.inl R (Fractions.normal R (c := c)) (Fractions.parameters R (m := m))) =
    Koszul.GeneratorMatrix.equation R s := by
  ext x
  simp [equation]

theorem equation_tuple {q : ℕ} (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q) (k : Fin q) :
    equation R s t (Fractions.tuple R (c := c) a k) = t (a.val k).down := by
  simp [equation, Fractions.tuple, Koszul.GeneratorMatrix.equation_apply, Pi.basisFun_apply,
    Pi.single_apply]

theorem differential (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (x : ⋀[R]^(p + 1) (Fractions.normal R (c := c))) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R _ (equation R s t)
        (insertionAt R (p + 1) (q + 1) (p + q + 2) (by omega) a x).val =
      (insertionAt R p (q + 1) (p + q + 1) rfl a
        (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x)).val +
      (-1 : R) ^ (p + 1) •
        (∑ k : Fin (q + 1), ((-1 : R) ^ k.val * t (a.val k).down) •
          (insertionAt R (p + 1) q (p + q + 1) (by omega) (a.delete k) x).val) := by
  have hn := LinearMap.congr_fun
    (Exterior.KoszulComplex.contraction_naturality R (Fractions.normal R (c := c)) (Fractions.ambient R (c := c) (m := m))
      (Koszul.GeneratorMatrix.equation R s) (equation R s t)
      (LinearMap.inl R _ _) (equation_inl R s t) p) x
  have hnc := congrArg Subtype.val hn
  simp only [LinearMap.comp_apply, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_coe] at hnc
  simp only [insertionAt_coe]
  rw [Contraction.homogeneous_mul, hnc, Koszul.CechEvaluation.ambient,
    Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [equation_tuple, mul_smul_comm]
  rfl

theorem contraction_identity (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (x : ⋀[R]^(p + 1) (Fractions.normal R (c := c))) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (equation R s t) (p + q + 1)
        (insertionAt R (p + 1) (q + 1) (p + q + 2) (by omega) a x) =
      insertionAt R p (q + 1) (p + q + 1) rfl a
        (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x) +
      (-1 : R) ^ (p + 1) •
        (∑ k : Fin (q + 1), ((-1 : R) ^ k.val * t (a.val k).down) •
          insertionAt R (p + 1) q (p + q + 1) (by omega) (a.delete k) x) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_sum]
  exact differential R s t p q a x

theorem dual_identity (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (φ : Module.Dual R (⋀[R]^(p + q + 1) (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^(p + 1) (Fractions.normal R (c := c))) :
    φ (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (equation R s t) (p + q + 1)
        (insertionAt R (p + 1) (q + 1) (p + q + 2) (by omega) a x)) =
      φ (insertionAt R p (q + 1) (p + q + 1) rfl a
        (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x)) +
      (-1 : R) ^ (p + 1) •
        (∑ k : Fin (q + 1), ((-1 : R) ^ k.val * t (a.val k).down) •
          φ (insertionAt R (p + 1) q (p + q + 1) (by omega) (a.delete k) x)) := by
  rw [contraction_identity, map_add, map_smul, map_sum]
  simp only [map_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
