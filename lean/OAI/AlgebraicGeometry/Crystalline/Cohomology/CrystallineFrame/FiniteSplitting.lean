import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Finite Splitting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FiniteSplitting.CrystallineFrameFiniteSplitting

noncomputable section

/-!
# Finite coefficient splittings of the actual frame-resolution terms

A basis of each finite exterior power gives natural coefficient
projections and inclusions. Their finite sum is the identity, both on
the original frame presheaves and after the prescribed sheafification.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X

local instance indexFintype (n : ℕ) : Fintype (Set.powersetCard σ n) := Fintype.ofFinite _

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) W (⋀[W]^n (σ →₀ W)) :=
  (Finsupp.basisSingleOne : Module.Basis σ W (σ →₀ W)).exteriorPower n

def projection (n : ℕ) (i : Set.powersetCard σ n) : (P).X n ⟶ F where
  app Q := ModuleCat.ofHom ((LinearMap.proj i).comp
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv W (Set.powersetCard σ n) ((F).obj Q)
      (⋀[W]^n (σ →₀ W)) (basis p k σ n)).toLinearMap)
  naturality := by
    intro Q T f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro ω
    change (basis p k σ n).equivFun ω i • ((F).map f).hom m =
      ((F).map f).hom ((basis p k σ n).equivFun ω i • m)
    exact (((F).map f).hom.map_smul _ _).symm

def inclusion (n : ℕ) (i : Set.powersetCard σ n) : F ⟶ (P).X n where
  app Q := ModuleCat.ofHom ((TensorProduct.mk W ((F).obj Q) (⋀[W]^n (σ →₀ W))).flip
    (basis p k σ n i))
  naturality := by
    intro Q T f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

theorem sum_identity (n : ℕ) :
    ∑ i, projection p k B σ a n i ≫ inclusion p k B σ a n i = 𝟙 ((P).X n) := by
  apply NatTrans.ext
  funext Q
  simp only [NatTrans.app_sum, NatTrans.comp_app]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum]
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  let z : ((P).X n).obj Q := m ⊗ₜ[W] ω
  change (∑ i, ((projection p k B σ a n i).app Q ≫
    (inclusion p k B σ a n i).app Q).hom) z = z
  rw [LinearMap.sum_apply]
  change ∑ i, ((basis p k σ n).equivFun ω i • m) ⊗ₜ[W] basis p k σ n i = m ⊗ₜ[W] ω
  simp_rw [TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, (basis p k σ n).sum_equivFun]

def sheafProjection (n : ℕ) (i : Set.powersetCard σ n) :
    (SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n ⟶ (S).obj F :=
  (S).map (projection p k B σ a n i)

def sheafInclusion (n : ℕ) (i : Set.powersetCard σ n) :
    (S).obj F ⟶ (SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n :=
  (S).map (inclusion p k B σ a n i)

theorem sheaf_sum_identity (n : ℕ) :
    ∑ i, sheafProjection p k B σ a n i ≫ sheafInclusion p k B σ a n i =
      𝟙 ((SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n) := by
  have h := congrArg (fun f => (S).map f) (sum_identity p k B σ a n)
  simp only [Functor.map_sum, Functor.map_comp] at h
  exact h.trans ((S).map_id ((P).X n))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FiniteSplitting.CrystallineFrameFiniteSplitting
