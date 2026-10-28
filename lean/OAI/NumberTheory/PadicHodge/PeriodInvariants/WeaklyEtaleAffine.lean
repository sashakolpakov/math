import Mathlib.RingTheory.Etale.Weakly
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Weakly Etale Affine -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffine

noncomputable section

/-! # Weakly etale algebras give actual weakly etale affine scheme morphisms -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe v
variable (R S : Type v) [CommRing R] [CommRing S] [Algebra R S] [Algebra.WeaklyEtale R S]

theorem specMap : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) where
  flat := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  flat_diagonal := by
    rw [diagonal_SpecMap R S]
    have : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := S)).toRingHom)) :=
      Flat.SpecMap_iff.mpr (Algebra.WeaklyEtale.flat_lmul' R S)
    infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffine
