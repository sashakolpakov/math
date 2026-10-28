import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RankOneDifferentialCoefficients

/-! # Rank One Dual Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RankOneDualPresentation

noncomputable section

/-! The dual of a rank-one differential presents precisely its coefficient ideal. Finite free duality also carries a zero scalar-extended differential to zero. -/
open _root_.Module
universe u
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

def rankOneDualCoefficientMap (e : R ≃ₗ[R] M) (f : M →ₗ[R] N) :
    Module.Dual R N →ₗ[R] R where
  toFun ℓ := ℓ (f (e 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rankOneDualCoefficientMap_ker (e : R ≃ₗ[R] M) (f : M →ₗ[R] N) :
    (rankOneDualCoefficientMap e f).ker = f.dualMap.ker := by
  ext ℓ
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    obtain ⟨r, rfl⟩ := e.surjective x
    have he : e r = r • e 1 := by
      simpa only [smul_eq_mul, mul_one] using e.map_smul r (1 : R)
    change ℓ (f (e r)) = 0
    change ℓ (f (e 1)) = 0 at h
    rw [he, f.map_smul, ℓ.map_smul, h, smul_zero]
  · intro h
    exact congrArg (fun z : Module.Dual R M => z (e 1)) h

theorem rankOneDualCoefficientMap_range
    {ι : Type u} [Fintype ι] (b : Basis ι R N) (e : R ≃ₗ[R] M) (f : M →ₗ[R] N) :
    (rankOneDualCoefficientMap e f).range =
      Ideal.span (Set.range fun i => b.repr (f (e 1)) i) := by
  classical
  let d := rankOneDualCoefficientMap e f
  calc
    d.range = (⊤ : Submodule R (Module.Dual R N)).map d := (Submodule.map_top d).symm
    _ = (Submodule.span R (Set.range b.dualBasis)).map d := by rw [b.dualBasis.span_eq]
    _ = Submodule.span R (Set.range fun i => d (b.dualBasis i)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = Ideal.span (Set.range fun i => b.repr (f (e 1)) i) := by
      exact congrArg (fun v : ι → R => Ideal.span (Set.range v))
        (funext fun i => b.dualBasis_apply i (f (e 1)))

theorem baseChange_dualMap_zero_of_zero
    (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : f.baseChange B = 0) : f.dualMap.baseChange B = 0 := by
  apply LinearMap.ext
  intro z
  apply (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B M).injective
  calc
    HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B M (f.dualMap.baseChange B z) =
        (f.baseChange B).dualMap (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B N z) :=
      congrArg (fun h => h z) (HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv_naturality B f)
    _ = 0 := by
      rw [hf]
      ext x
      simp [LinearMap.dualMap_apply]
    _ = HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B M 0 := (map_zero _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RankOneDualPresentation
