import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PEL

/-! # Base Change Coherence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence

noncomputable section

/-! Canonical group-preserving identifications of iterated base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T U : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

/-- The usual base-change associativity isomorphism lifted to group objects. -/
def baseChangeCompGroupIso (f : U ⟶ T) (h : T ⟶ S) :
    Grp.mk (A.pullback (f ≫ h)).scheme ≅ Grp.mk ((A.pullback h).pullback f).scheme :=
  (Functor.mapGrpNatIso (Over.pullbackComp f h)).app (Grp.mk A.scheme) ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback h) (G := Over.pullback f)).app
      (Grp.mk A.scheme)

/-- Equality of base arrows followed by the canonical base-change comparison. -/
def baseChangeFactorGroupIso (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S)
    (w : f ≫ h = x) :
    Grp.mk (A.pullback x).scheme ≅ Grp.mk ((A.pullback h).pullback f).scheme :=
  (eqToIso (congrArg (fun z => Grp.mk (A.pullback z).scheme) w)).symm ≪≫
    baseChangeCompGroupIso A f h

abbrev baseChangeFactorIso (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S)
    (w : f ≫ h = x) :
    (A.pullback x).scheme ≅ ((A.pullback h).pullback f).scheme :=
  (Grp.forget (Over U)).mapIso (baseChangeFactorGroupIso A f h x w)

instance baseChangeFactorIso_isMonHom (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S)
    (w : f ≫ h = x) : IsMonHom (baseChangeFactorIso A f h x w).hom :=
  (baseChangeFactorGroupIso A f h x w).hom.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChangeCoherence
