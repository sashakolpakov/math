import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FieldBaseChangePoints

/-! # Divisible Field Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DivisibleFieldBaseChange.Construction

noncomputable section

/-! Field extension of the actual q-divisible group in CMPoints's height
witness. The finite levels, closed inclusions, ranks, and defining
kernel equations are constructed and proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem mulEquiv_image_pow_transport {A B A' B' : Type*}
    [Group A] [Group B] [Group A'] [Group B']
    (eA : A' ≃* A) (eB : B' ≃* B) (f : A → B) (f' : A' → B')
    (hf : ∀ a, eB (f' a) = f (eA a)) (n : ℕ)
    (hker : ∀ b, (∃ a, f a = b) ↔ b ^ n = 1) (b : B') :
    (∃ a, f' a = b) ↔ b ^ n = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    apply eB.injective
    exact (map_pow eB b n).trans
      (((hker (eB b)).mp ⟨eA a, (hf a).symm.trans (congrArg eB ha)⟩).trans eB.map_one.symm)
  · intro hb
    have h : (eB b) ^ n = 1 :=
      (map_pow eB b n).symm.trans ((congrArg eB hb).trans eB.map_one)
    obtain ⟨a, ha⟩ := (hker (eB b)).mpr h
    refine ⟨eA.symm a, eB.injective ?_⟩
    exact (hf (eA.symm a)).trans ((congrArg f (eA.apply_symm_apply a)).trans ha)

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {p h : ℕ} (G : GroupSchemes.FiniteEtale.PDivisibleGroup k p h)

def pDivisibleGroupFieldBaseChange : GroupSchemes.FiniteEtale.PDivisibleGroup k' p h where
  level n := GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange (G.level n)
  inclusion n := FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap (k' := k') (G.inclusion n)
  inclusion_hom n := FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap_isMonHom (k' := k') (G.inclusion n)
  inclusion_closed n := FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap_closed (k' := k') (G.inclusion n)
  rank n := (GroupFieldBaseChange.Construction.finiteGroupFieldBaseChange_finrank (k' := k') (G.level n)).trans (G.rank n)
  kernel n R x := by
    let eA := ((FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level n)).app R).groupIsoToMulEquiv
    let eB := ((FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level (n + 1))).app R).groupIsoToMulEquiv
    exact mulEquiv_image_pow_transport eA eB (fun y => y ≫ G.inclusion n)
      (fun y => y ≫ FieldBaseChangeMaps.Construction.finiteGroupFieldBaseChangeSchemeMap (k' := k') (G.inclusion n))
      (fun y => FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso_postcomp (k' := k') (G.inclusion n) R y)
      (p ^ n) (G.kernel n (AffineFieldRestriction.Construction.restrictFieldAlgebra (k := k) R)) x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DivisibleFieldBaseChange.Construction
