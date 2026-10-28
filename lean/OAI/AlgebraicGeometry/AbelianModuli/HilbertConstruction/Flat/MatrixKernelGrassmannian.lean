import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.CokernelKernelBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientStalkRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization

/-! # Matrix Kernel Grassmannian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MatrixKernelGrassmannian

noncomputable section

/-! A finite matrix with flat cokernel of prescribed complementary
rank defines its kernel as an actual Grassmannian quotient. This
construction is natural under every coefficient-ring homomorphism. -/
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S μ ν : Type u} [CommRing R] [CommRing S]
variable [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

theorem matrixCokernel_projective_of_flat (F : Matrix ν μ R)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range)) :
    Module.Projective R ((ν → R) ⧸ (Matrix.toLin' F).range) := by
  obtain ⟨X, hX⟩ := (HilbertScheme.Presentations.CokernelSplittingEquation.matrix_cokernel_flat_iff_splitting_equation F).mp hflat
  apply (HilbertScheme.Presentations.CokernelSplittingEquation.cokernel_projective_iff_splitting_equation (Matrix.toLin' F)).mpr
  refine ⟨Matrix.toLin' X, ?_⟩
  simpa only [Matrix.toLin'_mul, LinearMap.comp_assoc] using congrArg Matrix.toLin' hX

theorem matrixRange_projective_of_flat_cokernel (F : Matrix ν μ R)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range)) :
    Module.Projective R (Matrix.toLin' F).range := by
  have := matrixCokernel_projective_of_flat F hflat
  obtain ⟨r, hr⟩ := HilbertScheme.Presentations.Projective.QuotientRetraction.exists_projective_quotient_retraction (Matrix.toLin' F).range
  exact Module.Projective.of_split (Matrix.toLin' F).range.subtype r hr

theorem matrixKernelQuotient_projective_of_flat_cokernel (F : Matrix ν μ R)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range)) :
    Module.Projective R ((μ → R) ⧸ (Matrix.toLin' F).ker) := by
  have := matrixRange_projective_of_flat_cokernel F hflat
  exact Module.Projective.of_equiv (Matrix.toLin' F).quotKerEquivRange.symm

theorem matrixKernelQuotient_rankAtStalk (F : Matrix ν μ R) (k : ℕ)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' F).range) p + k = Fintype.card ν)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ((μ → R) ⧸ (Matrix.toLin' F).ker) p = k := by
  have : Nontrivial R := ⟨⟨0, 1, fun h => p.isPrime.one_notMem (h ▸ p.asIdeal.zero_mem)⟩⟩
  have := matrixCokernel_projective_of_flat F hflat
  have := matrixRange_projective_of_flat_cokernel F hflat
  have hs := HilbertConstruction.Projective.QuotientStalkRank.projectiveQuotient_rankAtStalk_add (Matrix.toLin' F).range p
  rw [Module.rankAtStalk_eq_finrank_of_free (R := R) (M := ν → R),
    Module.finrank_fintype_fun_eq_card] at hs
  rw [congrFun (Module.rankAtStalk_eq_of_equiv (Matrix.toLin' F).quotKerEquivRange) p]
  exact Nat.add_left_cancel (hs.trans (hrank p).symm)

def flatMatrixKernelGrassmannian (F : Matrix ν μ R) (k : ℕ)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' F).range) p + k = Fintype.card ν) :
    Module.Grassmannian R (μ → R) k where
  toSubmodule := (Matrix.toLin' F).ker
  finite_quotient := inferInstance
  projective_quotient := matrixKernelQuotient_projective_of_flat_cokernel F hflat
  rankAtStalk_eq := matrixKernelQuotient_rankAtStalk F k hflat hrank

theorem matrixCokernel_flatRank_baseChange (φ : R →+* S) (F : Matrix ν μ R) (k : ℕ)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' F).range) p + k = Fintype.card ν) :
    Module.Flat S ((ν → S) ⧸ (Matrix.toLin' (F.map φ)).range) ∧
      ∀ p : PrimeSpectrum S, Module.rankAtStalk (R := S)
        ((ν → S) ⧸ (Matrix.toLin' (F.map φ)).range) p + k = Fintype.card ν := by
  let := φ.toAlgebra
  let := hflat
  let E := HilbertConstruction.Matrix.CokernelLocalization.matrixCokernelBaseChangeEquiv F S
  refine ⟨Module.Flat.of_linearEquiv E, fun p => ?_⟩
  change Module.rankAtStalk (R := S) ((ν → S) ⧸ (Matrix.toLin' (F.map (algebraMap R S))).range) p + k = _
  rw [congrFun (Module.rankAtStalk_eq_of_equiv E) p, Module.rankAtStalk_baseChange]
  exact hrank (p.comap φ)

theorem flatMatrixKernelGrassmannian_baseChange (φ : R →+* S) (F : Matrix ν μ R) (k : ℕ)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' F).range) p + k = Fintype.card ν) :
    HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ (flatMatrixKernelGrassmannian F k hflat hrank) =
      flatMatrixKernelGrassmannian (F.map φ) k
        (matrixCokernel_flatRank_baseChange φ F k hflat hrank).1
        (matrixCokernel_flatRank_baseChange φ F k hflat hrank).2 := by
  apply Module.Grassmannian.ext
  exact CokernelKernelBaseChange.matrix_kernel_baseChange_of_flat_cokernel φ F hflat

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MatrixKernelGrassmannian
