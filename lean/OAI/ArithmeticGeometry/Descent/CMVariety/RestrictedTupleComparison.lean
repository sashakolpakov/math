import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism

/-! # Restricted Tuple Comparison -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.RestrictedTupleComparison.Abelian

noncomputable section

/-! Exact group and tuple comparisons after restricting an arithmetic family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def restrictedAbelianFiberComparison
    {S T U : Scheme} {g : ℕ} (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g U) (e : (G.pullback p).scheme ≅ A.scheme) :
    ((G.pullback f).pullback h).scheme ≅ A.scheme :=
  AbelianCoefficientComparison.iteratedAbelianPullbackIso G f h p hp ≪≫ e

instance restrictedAbelianFiberComparison_group
    {S T U : Scheme} {g : ℕ} (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g U) (e : (G.pullback p).scheme ≅ A.scheme) [IsMonHom e.hom] :
    IsMonHom (restrictedAbelianFiberComparison G f h p hp A e).hom :=
  AbelianEndomorphism.abelian_iso_trans_group ((G.pullback f).pullback h) (G.pullback p) A
    (AbelianCoefficientComparison.iteratedAbelianPullbackIso G f h p hp) e
    (AbelianCoefficientComparison.iteratedAbelianPullbackIso_group G f h p hp) inferInstance

theorem restricted_tuple_comparison
    {Index : Type} {S T U : Scheme} {g : ℕ} (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : T ⟶ S) (h : U ⟶ T) (p : U ⟶ S) (hp : h ≫ f = p)
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g U) (e : (G.pullback p).scheme ≅ A.scheme)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple Index G) (k : AbelianEndomorphism.AbelianEndomorphismTuple Index A)
    (he : AbelianEndomorphism.ConjugateAbelianTuples e (a.pullback p) k) :
    AbelianEndomorphism.ConjugateAbelianTuples (restrictedAbelianFiberComparison G f h p hp A e)
      ((a.pullback f).pullback h) k :=
  AbelianEndomorphism.ConjugateAbelianTuples.trans (AbelianCoefficientComparison.iteratedAbelianPullbackIso G f h p hp) e
    ((a.pullback f).pullback h) (a.pullback p) k (a.pullback_comparison f h p hp) he

end

end OAI.ArithmeticGeometry.Descent.CMVariety.RestrictedTupleComparison.Abelian
