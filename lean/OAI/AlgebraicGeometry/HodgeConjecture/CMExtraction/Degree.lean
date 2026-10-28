import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeDegree
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Minuscule
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Degree -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Degree.Local

noncomputable section

/-! Determinant degrees of the actual GL3 minuscule operators. Three
central-normalized products have determinant degree one and therefore
belong to the determinant-zero sector. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

variable (q : ℕ) [Fact q.Prime]

abbrev GL3Degree := ℚ_[q]ˣ ⧸ RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q

def gl3DeterminantDegree : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q →* GL3Degree q :=
  (QuotientGroup.mk' (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q)).comp Matrix.GeneralLinearGroup.det

theorem gl3DeterminantDegree_integral (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :
    gl3DeterminantDegree q g = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralGL_unitDet q hg)

abbrev IsGL3Homogeneous (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) (a : GL3Degree q) : Prop :=
  HeckeDegree.Local.IsHomogeneousHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (gl3DeterminantDegree q) (gl3DeterminantDegree_integral q) T a

def gl3PrimeDegree : GL3Degree q := QuotientGroup.mk (AbelianScheme.TateComparison.HeckeKernel.qUnit q)

theorem gl3MinusculeRepresentative_det (k : Fin 4) :
    Matrix.GeneralLinearGroup.det (Minuscule.Local.gl3MinusculeRepresentative q k) = AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ k.val := by
  apply Units.ext
  change (Minuscule.Local.gl3MinusculeRepresentative q k).val.det = ((AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ k.val : ℚ_[q]ˣ) : ℚ_[q])
  fin_cases k <;> simp [Minuscule.Local.gl3MinusculeRepresentative, AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.det_diagonal,
    Fin.prod_univ_three, pow_succ]

theorem gl3MinusculeRepresentative_degree (k : Fin 4) :
    gl3DeterminantDegree q (Minuscule.Local.gl3MinusculeRepresentative q k) = gl3PrimeDegree q ^ k.val := by
  change QuotientGroup.mk' (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q)
    (Matrix.GeneralLinearGroup.det (Minuscule.Local.gl3MinusculeRepresentative q k)) = _
  rw [gl3MinusculeRepresentative_det, map_pow]
  rfl

theorem gl3MinusculeHecke_homogeneous (k : Fin 4) :
    IsGL3Homogeneous q (Minuscule.Local.gl3MinusculeHecke q k) (gl3PrimeDegree q ^ k.val)⁻¹ := by
  have h := HeckeDegree.Local.rawHecke_homogeneous (G := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (C := GL3Degree q)
    (U := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (d := gl3DeterminantDegree q)
    (hd := gl3DeterminantDegree_integral q) (Operators.Local.rawGL3Hecke_isRaw q (Minuscule.Local.gl3MinusculeRepresentative q k))
  rwa [gl3MinusculeRepresentative_degree] at h

theorem gl3Minuscule_three_scalar : Minuscule.Local.gl3MinusculeRepresentative q 3 =
    Matrix.GeneralLinearGroup.scalar (Fin 3) (AbelianScheme.TateComparison.HeckeKernel.qUnit q) := by
  apply Units.ext
  simp [Minuscule.Local.gl3MinusculeRepresentative, AbelianScheme.TateComparison.HeckeKernel.diagonalUnit]

theorem gl3Minuscule_three_commutes (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) : Commute g (Minuscule.Local.gl3MinusculeRepresentative q 3) := by
  rw [gl3Minuscule_three_scalar]
  apply Units.ext
  change g.val * Matrix.diagonal (fun _ => (AbelianScheme.TateComparison.HeckeKernel.qUnit q : ℚ_[q])) =
    Matrix.diagonal (fun _ => (AbelianScheme.TateComparison.HeckeKernel.qUnit q : ℚ_[q])) * g.val
  ext i j
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

def gl3CentralUnit : (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))ˣ :=
  AbelianScheme.TateComparison.HeckeKernel.centralHeckeUnit (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (Minuscule.Local.gl3MinusculeRepresentative q 3) (gl3Minuscule_three_commutes q)

theorem gl3CentralUnit_val : (gl3CentralUnit q).val = Minuscule.Local.gl3MinusculeHecke q 3 :=
  AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique _ (AbelianScheme.TateComparison.CentralConvolution.centralHeckeUnit_isRaw _ _ _) (Operators.Local.rawGL3Hecke_isRaw q _)

theorem gl3CentralUnit_inverse_homogeneous :
    IsGL3Homogeneous q (gl3CentralUnit q).inv (gl3PrimeDegree q ^ 3) := by
  change AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (gl3CentralUnit q).inv ∈ _
  have hk : AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (gl3CentralUnit q).inv =
      Finsupp.single (QuotientGroup.mk (Minuscule.Local.gl3MinusculeRepresentative q 3)) 1 := by
    simp [AbelianScheme.TateComparison.HeckeKernel.kernel, gl3CentralUnit, AbelianScheme.TateComparison.HeckeKernel.centralHeckeUnit, AbelianScheme.TateComparison.HeckeKernel.centralTranslation,
      AbelianScheme.TateComparison.HeckeKernel.translate]
  rw [hk]
  apply Finsupp.single_mem_supported ℚ 1
  exact gl3MinusculeRepresentative_degree q 3

theorem gl3_first_cube_degree_one :
    IsGL3Homogeneous q ((Minuscule.Local.gl3MinusculeHecke q 1) ^ 3 * (gl3CentralUnit q).inv) 1 := by
  have h := HeckeDegree.Local.homogeneousHecke_mul _ _ _
    (HeckeDegree.Local.homogeneousHecke_pow _ _ _ (gl3MinusculeHecke_homogeneous q 1) 3)
    (gl3CentralUnit_inverse_homogeneous q)
  simpa only [Fin.val_one, pow_one, inv_pow, inv_mul_cancel] using h

theorem gl3_second_cube_degree_one :
    IsGL3Homogeneous q ((Minuscule.Local.gl3MinusculeHecke q 2) ^ 3 * (gl3CentralUnit q).inv ^ 2) 1 := by
  have h := HeckeDegree.Local.homogeneousHecke_mul _ _ _
    (HeckeDegree.Local.homogeneousHecke_pow _ _ _ (gl3MinusculeHecke_homogeneous q 2) 3)
    (HeckeDegree.Local.homogeneousHecke_pow _ _ _ (gl3CentralUnit_inverse_homogeneous q) 2)
  have he : ((gl3PrimeDegree q ^ (2 : Fin 4).val)⁻¹) ^ 3 * (gl3PrimeDegree q ^ 3) ^ 2 = 1 := by
    rw [inv_pow, ← pow_mul, ← pow_mul]
    norm_num
  rwa [he] at h

theorem gl3_mixed_degree_one :
    IsGL3Homogeneous q (Minuscule.Local.gl3MinusculeHecke q 1 * Minuscule.Local.gl3MinusculeHecke q 2 * (gl3CentralUnit q).inv) 1 := by
  have h := HeckeDegree.Local.homogeneousHecke_mul _ _ _
    (HeckeDegree.Local.homogeneousHecke_mul _ _ _ (gl3MinusculeHecke_homogeneous q 1) (gl3MinusculeHecke_homogeneous q 2))
    (gl3CentralUnit_inverse_homogeneous q)
  have he : (gl3PrimeDegree q ^ (1 : Fin 4).val)⁻¹ *
      (gl3PrimeDegree q ^ (2 : Fin 4).val)⁻¹ * gl3PrimeDegree q ^ 3 = 1 := by
    norm_num only [Fin.val_one, Fin.val_ofNat]
    rw [← mul_inv, ← pow_add]
    norm_num
  rwa [he] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Degree.Local
