import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential

/-! # Cech Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential

noncomputable section

/-! After division by the canonical parameter units, the mixed Koszul
differential is exactly the differential of the supported Čech total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
private theorem fraction_identity {A : Type*} [CommRing A]
    (d u v t z e z' : A) (hc : t * d = e) (hz : z' = z) :
    d * (u * (v * t * z)) = u * (v * (e * z')) := by
  rw [hz, ← hc]
  ring
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Differential
open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C)
  (t : Fin m → R) (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def value (p q d : ℕ) (h : p + q = d) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q)
    (φ : Module.Dual R (⋀[R]^d (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^p (Fractions.normal R (c := c))) : P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)) :=
  Fractions.reciprocal R P U t ht a * algebraMap R _ (φ (Differential.insertionAt R p q d h a x))

theorem cancel {q : ℕ} (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1)) (k : Fin (q + 1)) :
    algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj a))) (t (a.val k).down) *
        Fractions.reciprocal R P U t ht a =
      (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom (Fractions.reciprocal R P U t ht (a.delete k)) :=
  Cech.DenominatorUnits.cancellation U (Fractions.rings R P) R (Fractions.scalars R P) (fun i => t i.down) ht a k

variable (s : Fin c → R)

theorem differential (p q : ℕ) (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) (q + 1))
    (φ : Module.Dual R (⋀[R]^(p + q + 1) (Fractions.ambient R (c := c) (m := m))))
    (x : ⋀[R]^(p + 1) (Fractions.normal R (c := c))) :
    value R P U t ht (p + 1) (q + 1) (p + q + 2) (by omega) a
        (φ.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Differential.equation R s t) (p + q + 1))) x =
      value R P U t ht p (q + 1) (p + q + 1) rfl a φ
        (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) p x) +
      (-1 : R) ^ (p + 1) •
        (∑ k : Fin (q + 1), (-1 : R) ^ k.val •
          (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom
            (value R P U t ht (p + 1) q (p + q + 1) (by omega) (a.delete k) φ x)) := by
  simp only [value, LinearMap.comp_apply]
  rw [Differential.dual_identity, map_add, mul_add]
  congr 1
  simp only [smul_eq_mul, Algebra.smul_def, map_mul, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hα : (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom
      (algebraMap R _ (φ (Differential.insertionAt R (p + 1) q (p + q + 1) (by omega) (a.delete k) x))) =
      algebraMap R _ (φ (Differential.insertionAt R (p + 1) q (p + q + 1) (by omega) (a.delete k) x)) :=
    (P.map ((AugmentedOrdered.Cech.face U q k).φ a).op).hom.commutes _
  exact fraction_identity _ _ _ _ _ _ _ (cancel R P U t ht a k) hα

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CechDifferential
