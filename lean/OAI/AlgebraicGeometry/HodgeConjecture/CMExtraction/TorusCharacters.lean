import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Satake
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Degree
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange

/-! # Torus Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TorusCharacters.Iwasawa

noncomputable section

/-! Actual GL3 torus characters extend the computed SL3 character. The
central value explicitly records the inverse-representative convention
of the raw Hecke kernel. -/

open scoped Classical BigOperators

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Degree.Local

variable (q : ℕ) [Fact q.Prime]

def gl3TorusSatakeOver {F : Type*} [Field F] [Algebra ℚ F] (t : Fin 3 → Fˣ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ] F :=
  (SatakeBaseChange.Iwasawa.rationalLatticeEvaluation t).comp (Satake.Iwasawa.gl3RationalSatake q)

theorem gl3TorusSatakeOver_sl3 {F : Type*} [Field F] [Algebra ℚ F]
    (t : Fin 3 → Fˣ) {s : ℕ} (v : Fin s) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    gl3TorusSatakeOver q t (Retraction.Local.sl3ToGL3Hecke q v T) = SatakeBaseChange.Iwasawa.torusSatakeOver q t T := by
  change SatakeBaseChange.Iwasawa.rationalLatticeEvaluation t (Satake.Iwasawa.gl3RationalSatake q (Retraction.Local.sl3ToGL3Hecke q v T)) = _
  rw [Satake.Iwasawa.gl3RationalSatake_sl3]
  rfl

theorem gl3RationalSatake_coeff (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (ell : Fin 3 → ℤ) :
    (Satake.Iwasawa.gl3RationalSatake q T).coeff ell =
      Finsupp.mapDomain (Iwasawa.gl3Decomposition q).height (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) ell *
        (q : ℚ) ^ (ell 2 - ell 0) := rfl

theorem gl3_central_inverse_height :
    (Iwasawa.gl3Decomposition q).height (QuotientGroup.mk (Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹) =
      fun _ => -1 := by
  have htri : Minuscule.Local.gl3MinusculeRepresentative q 3 ∈ RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q] := by
    intro i j hij
    change Matrix.diagonal _ i j = 0
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  let b : (Iwasawa.gl3Decomposition q).B :=
    ⟨(Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹, (RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q]).inv_mem htri⟩
  change (Iwasawa.gl3Decomposition q).height (QuotientGroup.mk b.val) = _
  rw [RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition.height_mk]
  funext i
  change (((Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹).val i i).valuation = -1
  rw [Degree.Local.gl3Minuscule_three_scalar,
    ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 3)) (AbelianScheme.TateComparison.HeckeKernel.qUnit q)]
  change (Matrix.diagonal (fun _ : Fin 3 => ((AbelianScheme.TateComparison.HeckeKernel.qUnit q)⁻¹ : ℚ_[q]ˣ).val) i i).valuation = -1
  rw [Matrix.diagonal_apply_eq]
  change ((q : ℚ_[q])⁻¹).valuation = -1
  rw [Padic.valuation_inv, Padic.valuation_p]

theorem gl3RationalSatake_central :
    Satake.Iwasawa.gl3RationalSatake q (Minuscule.Local.gl3MinusculeHecke q 3) =
      AddMonoidAlgebra.single (fun _ : Fin 3 => (-1 : ℤ)) 1 := by
  have hk : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Minuscule.Local.gl3MinusculeHecke q 3) =
      Finsupp.single (QuotientGroup.mk (Minuscule.Local.gl3MinusculeRepresentative q 3)⁻¹) 1 := by
    rw [← Degree.Local.gl3CentralUnit_val]
    exact AbelianScheme.TateComparison.HeckeKernel.centralHeckeUnit_kernel _ _ _
  ext ell
  rw [gl3RationalSatake_coeff, hk, Finsupp.mapDomain_single, gl3_central_inverse_height]
  by_cases he : ell = fun _ => (-1 : ℤ)
  · subst ell
    simp
  · simp [he]

theorem gl3TorusSatakeOver_central {F : Type*} [Field F] [Algebra ℚ F] (t : Fin 3 → Fˣ) :
    gl3TorusSatakeOver q t (Minuscule.Local.gl3MinusculeHecke q 3) =
      ((t 0 : F) * (t 1 : F) * (t 2 : F))⁻¹ := by
  change SatakeBaseChange.Iwasawa.rationalLatticeEvaluation t (Satake.Iwasawa.gl3RationalSatake q (Minuscule.Local.gl3MinusculeHecke q 3)) = _
  rw [gl3RationalSatake_central]
  simp [SatakeBaseChange.Iwasawa.rationalLatticeEvaluation, AddMonoidAlgebra.lift_single, SatakeBaseChange.Iwasawa.torusCharacterOver,
    Fin.prod_univ_three]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TorusCharacters.Iwasawa
