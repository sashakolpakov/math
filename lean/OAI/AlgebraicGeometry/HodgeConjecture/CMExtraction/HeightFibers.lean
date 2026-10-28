import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BorelCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicUnitValuation

/-! # Height Fibers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeightFibers.Iwasawa

noncomputable section

/-! The fibre of the actual Iwasawa height is precisely the unipotent
orbit of the indicated diagonal prime-power coset. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

def gl3Torus (ell : Fin 3 → ℤ) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q := AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ell i)

theorem gl3Torus_integral_diagonal (u : Fin 3 → ℤ_[q]ˣ) :
    AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom (u i)) ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q := by
  refine ⟨AbelianScheme.TateComparison.HeckeKernel.diagonalUnit u, ?_⟩
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit]
  · simp [AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.diagonal_apply_ne _ hij]

theorem gl3Torus_unipotent_height (ell : Fin 3 → ℤ) (x y z : ℚ_[q]) :
    (Iwasawa.gl3Decomposition q).height (QuotientGroup.mk (gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z)) = ell := by
  have ht : gl3Torus q ell ∈ RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q] := by
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  let b : (Iwasawa.gl3Decomposition q).B :=
    ⟨gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z, (RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q]).mul_mem ht
      (Unipotent.Iwasawa.gl3Unipotent_upper q x y z)⟩
  change (Iwasawa.gl3Decomposition q).height (QuotientGroup.mk b.val) = _
  rw [RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.height_mk]
  funext i
  change ((gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z).val i i).valuation = ell i
  rw [show (gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z).val =
    RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.triangular (q : ℚ_[q]) ell x y z from Unipotent.Iwasawa.gl3Torus_mul_unipotent q ell x y z]
  fin_cases i <;> simp [RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.triangular, Padic.valuation_zpow]

theorem gl3_height_fiber (ell : Fin 3 → ℤ)
    (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :
    (Iwasawa.gl3Decomposition q).height c = ell ↔
      ∃ x y z : ℚ_[q], QuotientGroup.mk (gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent x y z) = c := by
  constructor
  · obtain ⟨b, rfl⟩ := (Iwasawa.gl3Decomposition q).exists_representative c
    intro he
    have hv (i : Fin 3) : (b.val.val i i).valuation = ell i := by
      rw [RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.height_mk] at he
      exact congrFun he i
    have hu (i : Fin 3) : ∃ u : ℤ_[q]ˣ, RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b i =
        AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ell i * Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom u := by
      obtain ⟨u, hu⟩ := PadicUnitValuation.Iwasawa.padic_unit_valuation_factorization q (RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b i)
      refine ⟨u, ?_⟩
      change RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b i = AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (b.val.val i i).valuation * _ at hu
      rwa [hv] at hu
    choose u hu using hu
    let U : Fin 3 → ℚ_[q]ˣ := fun i => Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom (u i)
    let x := b.val.val 0 1 / b.val.val 0 0
    let y := b.val.val 0 2 / b.val.val 0 0
    let z := b.val.val 1 2 / b.val.val 1 1
    let a := (U 0 : ℚ_[q]) / (U 1 : ℚ_[q]) * x
    let d := (U 0 : ℚ_[q]) / (U 2 : ℚ_[q]) * y
    let f := (U 1 : ℚ_[q]) / (U 2 : ℚ_[q]) * z
    have hb : b.val = (gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a d f) * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit U := by
      have hdiag : RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b = fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ ell i * U i := funext hu
      calc b.val = AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q] b) * Unipotent.Iwasawa.gl3Unipotent x y z :=
             BorelCoordinates.Iwasawa.gl3Borel_factorization b
           _ = (gl3Torus q ell * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit U) * Unipotent.Iwasawa.gl3Unipotent x y z := by
             rw [hdiag, ← BorelCoordinates.Iwasawa.gl3_diagonal_mul]
             rfl
           _ = (gl3Torus q ell * Unipotent.Iwasawa.gl3Unipotent a d f) * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit U := by
             rw [mul_assoc, BorelCoordinates.Iwasawa.gl3_diagonal_unipotent_commute, ← mul_assoc]
    refine ⟨a, d, f, ?_⟩
    rw [hb]
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using gl3Torus_integral_diagonal q u
  · rintro ⟨x, y, z, rfl⟩
    exact gl3Torus_unipotent_height q ell x y z

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeightFibers.Iwasawa
