import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Base Change Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Identity and composition comparisons for the abelian-scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S S' S'' : Scheme.{u}}

/-- Composition of base changes, first as an isomorphism of monoid objects. -/
def Schemes.AbelianScheme.pullbackCompMonIso (A : Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    Mon.mk (A.pullback (h ≫ f)).scheme ≅ Mon.mk ((A.pullback f).pullback h).scheme :=
  (Functor.mapMonNatIso (Over.pullbackComp h f)).app (Mon.mk A.scheme) ≪≫
    (Functor.mapMonCompIso (F := Over.pullback f) (G := Over.pullback h)).app (Mon.mk A.scheme)

/-- The canonical isomorphism between iterated and composite base change. -/
def Schemes.AbelianScheme.pullbackCompIso (A : Schemes.AbelianScheme g S) (f : S' ⟶ S) (h : S'' ⟶ S') :
    (A.pullback (h ≫ f)).scheme ≅ ((A.pullback f).pullback h).scheme :=
  (Mon.forget (Over S'')).mapIso (A.pullbackCompMonIso f h)

instance Schemes.AbelianScheme.pullbackCompIso_preservesGroup (A : Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') : IsMonHom (A.pullbackCompIso f h).hom :=
  inferInstanceAs (IsMonHom (A.pullbackCompMonIso f h).hom.hom)

/-- Pulling back along the identity, as an isomorphism of monoid objects. -/
def Schemes.AbelianScheme.pullbackIdMonIso (A : Schemes.AbelianScheme g S) :
    Mon.mk (A.pullback (𝟙 S)).scheme ≅ Mon.mk A.scheme :=
  (Functor.mapMonNatIso Over.pullbackId).app (Mon.mk A.scheme) ≪≫
    (Functor.mapMonIdIso (C := Over S)).app (Mon.mk A.scheme)

/-- Identity base change gives the original abelian scheme. -/
def Schemes.AbelianScheme.pullbackIdIso (A : Schemes.AbelianScheme g S) : (A.pullback (𝟙 S)).scheme ≅ A.scheme :=
  (Mon.forget (Over S)).mapIso A.pullbackIdMonIso

instance Schemes.AbelianScheme.pullbackIdIso_preservesGroup (A : Schemes.AbelianScheme g S) :
    IsMonHom A.pullbackIdIso.hom :=
  inferInstanceAs (IsMonHom A.pullbackIdMonIso.hom.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
