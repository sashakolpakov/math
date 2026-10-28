import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Tensor Point Topology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TensorPointTopology

noncomputable section

/-!
# Actual complex points of tensor products

The universal algebra lift is continuous in both characters for their
evaluation topologies. This gives the product topology needed when
transferring separatedness of schemes to their complex points.
-/

open scoped TensorProduct

variable (A B : Type) [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

def tensorPoint (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) :=
  Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => Commute.all _ _)

theorem tensorPoint_continuous : Continuous (tensorPoint A B) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    exact ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_fst).mul
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval b).comp continuous_snd)
  | add a b ha hb =>
    exact (ha.add hb).congr (fun p => (map_add (tensorPoint A B p) a b).symm)

def tensorPointsHomeomorph : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[ℂ] B) ≃ₜ
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints A × Foundations.Scheme.AffineComplexPoints.affineComplexPoints B where
  toFun p := (p.comp Algebra.TensorProduct.includeLeft,
    p.comp Algebra.TensorProduct.includeRight)
  invFun := tensorPoint A B
  left_inv p := by
    apply Algebra.TensorProduct.ext
    · exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
    · exact Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _)
  right_inv p := by
    apply Prod.ext
    · exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
    · exact Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _)
  continuous_toFun :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] A ⊗[ℂ] B)).continuous.prodMk
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] A ⊗[ℂ] B)).continuous
  continuous_invFun := tensorPoint_continuous A B

end

end OAI.AlgebraicGeometry.Comparison.Betti.TensorPointTopology
