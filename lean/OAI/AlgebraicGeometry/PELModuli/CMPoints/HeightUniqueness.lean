import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization

/-! # Height Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightUniqueness

noncomputable section

/-! Height is determined by the actual block functor, independently of
its chosen finite affine presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def commutativePointIsoOfGroupIso {k : Type} [Field k]
    {G H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k}
    (e : G.points ⋙ forget₂ CommGrpCat GrpCat ≅ H.points ⋙ forget₂ CommGrpCat GrpCat) :
    G.points ≅ H.points :=
  NatIso.ofComponents (fun R => ((e.app R).groupIsoToMulEquiv).toCommGrpIso) (by
    intro R S f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom (e.hom.naturality f) x)

theorem blockHasHeight_unique
    {k O : Type} [Field k] [CommRing O] {g q h h' : ℕ} [Fact q.Prime]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (χ : O →+* PadicInt q) (hG : BlocksProjectors.BlockHasHeight A ρ χ h) (hH : BlocksProjectors.BlockHasHeight A ρ χ h') :
    h = h' := by
  obtain ⟨G, eG, _⟩ := hG
  obtain ⟨H, eH, _⟩ := hH
  let e := GroupSchemes.FiniteEtale.FiniteCommGroupScheme.schemeIsoOfPoints
    (commutativePointIsoOfGroupIso (eG 1 ≪≫ (eH 1).symm))
  have hr := RankSpecialization.finite_group_rank_of_iso (G.level 1) (H.level 1) e
  rw [G.rank, H.rank, Nat.one_mul, Nat.one_mul] at hr
  exact Nat.pow_right_injective (Fact.out : q.Prime).two_le hr

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightUniqueness
