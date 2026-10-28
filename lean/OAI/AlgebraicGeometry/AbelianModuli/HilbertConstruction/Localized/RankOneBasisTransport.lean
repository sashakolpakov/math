import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisTransport

/-! # Rank One Basis Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.RankOneBasisTransport

noncomputable section

/-! An actual rank-one basis of the canonical localization transports to any realization of the localized ring and module. -/

def localizedRankOneBasisTransport {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) {R' M' : Type*} [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (e : LocalizedModule S M ≃ₗ[Localization S] Localization S) : M' ≃ₗ[R'] R' :=
  (BasisTransport.localizedBasisTransport S f ((Module.Basis.singleton Unit (Localization S)).map e.symm)).equivFun ≪≫ₗ
    LinearEquiv.funUnique Unit R' R'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.RankOneBasisTransport
