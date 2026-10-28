import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralTransform
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Central Minuscule -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralMinuscule.Iwasawa

noncomputable section

/-! Central translation and integral reversal relate the positive matrix
minuscule indicators to the original native raw minuscule operators. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

variable (q : ℕ) [Fact q.Prime]

def gl3TorusHom : Multiplicative (Fin 3 → ℤ) →* RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q where
  toFun a := HeightFibers.Iwasawa.gl3Torus q a.toAdd
  map_one' := by
    apply Units.ext
    simp [HeightFibers.Iwasawa.gl3Torus, AbelianScheme.TateComparison.HeckeKernel.diagonalUnit]
  map_mul' a b := by
    change AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (a.toAdd i + b.toAdd i)) =
      AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.toAdd i) * AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ b.toAdd i)
    rw [BorelCoordinates.Iwasawa.gl3_diagonal_mul]
    congr 1
    funext i
    exact zpow_add _ _ _

theorem gl3_central_torus : Minuscule.Local.gl3MinusculeRepresentative q 3 = HeightFibers.Iwasawa.gl3Torus q (fun _ => 1) := by
  simp [Minuscule.Local.gl3MinusculeRepresentative, HeightFibers.Iwasawa.gl3Torus]

theorem gl3_central_inverse_product (a : Fin 3 → ℤ) :
    ((Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹ * HeightFibers.Iwasawa.gl3Torus q a)⁻¹ = HeightFibers.Iwasawa.gl3Torus q (fun i => 1 - a i) := by
  rw [gl3_central_torus]
  change (((gl3TorusHom q) (Multiplicative.ofAdd (fun _ => 1)))⁻¹ *
    (gl3TorusHom q) (Multiplicative.ofAdd a))⁻¹ = _
  rw [← map_inv (gl3TorusHom q), ← map_mul, ← map_inv (gl3TorusHom q)]
  apply congrArg (gl3TorusHom q)
  apply Multiplicative.toAdd.injective
  funext i
  change -(-1 + a i) = 1 - a i
  ring

theorem gl3_central_inverse_positive (a : Fin 3 → ℤ) :
    (Degree.Local.gl3CentralUnit q).inv * Operators.Local.rawGL3Hecke q (HeightFibers.Iwasawa.gl3Torus q a) =
      IntegralTransform.Iwasawa.positiveGL3Hecke q (fun i => 1 - a i) := by
  let z := Minuscule.Local.gl3MinusculeRepresentative q 3
  have hz : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q, Commute g z⁻¹ := fun g => (Degree.Local.gl3Minuscule_three_commutes q g).inv_right
  have hu : (AbelianScheme.TateComparison.HeckeKernel.centralHeckeUnit (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) z⁻¹ hz).val = (Degree.Local.gl3CentralUnit q).inv := by
    apply Subtype.ext
    change AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (z⁻¹)⁻¹ =
      AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) z
    rw [inv_inv]
  have hraw := AbelianScheme.TateComparison.CentralConvolution.central_mul_isRaw (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) z⁻¹ hz (Operators.Local.rawGL3Hecke_isRaw q (HeightFibers.Iwasawa.gl3Torus q a))
  rw [hu] at hraw
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
  ext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [hraw g, IntegralTransform.Iwasawa.positiveGL3Hecke_kernel]
  change (if ∃ k l : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q,
      g = k.val * ((Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹ * HeightFibers.Iwasawa.gl3Torus q a)⁻¹ * l.val then 1 else 0) = _
  rw [gl3_central_inverse_product, IntegralTransform.Iwasawa.gl3_positive_doubleCoset_iff]

theorem positiveGL3Hecke_reverse (a : Fin 3 → ℤ) :
    IntegralTransform.Iwasawa.positiveGL3Hecke q a = IntegralTransform.Iwasawa.positiveGL3Hecke q ![a 2, a 1, a 0] := by
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
  ext c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [IntegralTransform.Iwasawa.positiveGL3Hecke_kernel, IntegralTransform.Iwasawa.positiveGL3Hecke_kernel]
  have he : RepresentationTheory.Hecke.DoubleCoset.Calculus.InDoubleCoset (q : ℤ_[q]) a g.val ↔
      RepresentationTheory.Hecke.DoubleCoset.Calculus.InDoubleCoset (q : ℤ_[q]) ![a 2, a 1, a 0] g.val := by
    constructor
    · exact RepresentationTheory.Hecke.DoubleCoset.Calculus.inDoubleCoset_reverse _ _ _
    · intro h
      have h' := RepresentationTheory.Hecke.DoubleCoset.Calculus.inDoubleCoset_reverse (q : ℤ_[q]) ![a 2, a 1, a 0] g.val h
      have ha : (![(![a 2, a 1, a 0] : Fin 3 → ℤ) 2,
          (![a 2, a 1, a 0] : Fin 3 → ℤ) 1, (![a 2, a 1, a 0] : Fin 3 → ℤ) 0] : Fin 3 → ℤ) = a := by
        ext i; fin_cases i <;> rfl
      rwa [ha] at h'
  rw [he]

theorem gl3_central_inverse_first :
    (Degree.Local.gl3CentralUnit q).inv * Minuscule.Local.gl3MinusculeHecke q 1 = IntegralTransform.Iwasawa.positiveGL3Hecke q ![1, 1, 0] := by
  have ha : Minuscule.Local.gl3MinusculeRepresentative q 1 = HeightFibers.Iwasawa.gl3Torus q ![1, 0, 0] := by
    unfold Minuscule.Local.gl3MinusculeRepresentative HeightFibers.Iwasawa.gl3Torus
    congr 1
    funext i
    fin_cases i <;> rfl
  change (Degree.Local.gl3CentralUnit q).inv * Operators.Local.rawGL3Hecke q (Minuscule.Local.gl3MinusculeRepresentative q 1) = _
  rw [ha, gl3_central_inverse_positive, positiveGL3Hecke_reverse]
  congr 1

theorem gl3_central_inverse_second :
    (Degree.Local.gl3CentralUnit q).inv * Minuscule.Local.gl3MinusculeHecke q 2 = IntegralTransform.Iwasawa.positiveGL3Hecke q ![1, 0, 0] := by
  have ha : Minuscule.Local.gl3MinusculeRepresentative q 2 = HeightFibers.Iwasawa.gl3Torus q ![1, 1, 0] := by
    unfold Minuscule.Local.gl3MinusculeRepresentative HeightFibers.Iwasawa.gl3Torus
    congr 1
    funext i
    fin_cases i <;> rfl
  change (Degree.Local.gl3CentralUnit q).inv * Operators.Local.rawGL3Hecke q (Minuscule.Local.gl3MinusculeRepresentative q 2) = _
  rw [ha, gl3_central_inverse_positive, positiveGL3Hecke_reverse]
  congr 1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralMinuscule.Iwasawa
