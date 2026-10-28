import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelUniversalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TransportComposition

/-! # Level Data Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelDataRecovery

noncomputable section

/-! Every native full-level Hilbert datum recovers the universal abelian
family and its level, with equality transport preserving both structures. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance fullLevelTransportComposite_isMonHom {S : Scheme.{u}} {g : ℕ}
    {A B C : Abelian.Schemes.AbelianScheme g S} (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (d : B.scheme ≅ C.scheme) [IsMonHom d.hom] : IsMonHom (e ≪≫ d).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ d.hom))

private theorem fullLevel_transport_comp_eq {S : Scheme.{u}} {g N : ℕ}
    {A B C : Abelian.Schemes.AbelianScheme g S} (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (d : B.scheme ≅ C.scheme) [IsMonHom d.hom]
    (l : A.FullLevel N) (m : B.FullLevel N) (t : C.FullLevel N)
    (h : l.transport e = m) (ht : m.transport d = t) :
    l.transport (e ≪≫ d) = t :=
  (Abelian.Schemes.AbelianScheme.FullLevel.transport_trans e d l).symm.trans
    ((congrArg (fun v : B.FullLevel N => v.transport d) h).trans ht)

section Equality
variable {S : Scheme.{u}} {g N : ℕ} {A B : Level.Data.AbelianSchemeWithFullLevel g N S}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso (h : A = B) : A.abelian.scheme ≅ B.abelian.scheme :=
  Abelian.Schemes.AbelianScheme.eqSchemeIso (congrArg Level.Data.AbelianSchemeWithFullLevel.abelian h)

instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso_isMonHom (h : A = B) :
    IsMonHom (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso h).hom :=
  Abelian.Schemes.AbelianScheme.eqSchemeIso_isMonHom (congrArg Level.Data.AbelianSchemeWithFullLevel.abelian h)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso_level (h : A = B) :
    A.level.transport (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso h) = B.level := by
  subst B
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  exact Category.comp_id _
end Equality

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)
variable (N : ℕ) [NeZero N]

def FixedDimensionHilbertFullLevelData (T : Over S) :=
  Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N

def FixedDimensionHilbertFullLevelData.family {T : Over S}
    (D : FixedDimensionHilbertFullLevelData S n P g Pm Pi N T) : Level.Data.AbelianSchemeWithFullLevel g N T.left :=
  ⟨(FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback D.1.left, D.2⟩

variable {T : Over S} (D : FixedDimensionHilbertFullLevelData S n P g Pm Pi N T)

def fixedDimensionHilbertFullLevelDataFamilyIso :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D).left).scheme ≅
        (D.family S n P g Pm Pi N).abelian.scheme :=
  LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D) ≪≫
      Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso
        (congrArg (fun E : FixedDimensionHilbertFullLevelData S n P g Pm Pi N T =>
          E.family S n P g Pm Pi N)
          ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).apply_symm_apply D))

instance fixedDimensionHilbertFullLevelDataFamilyIso_isMonHom :
    IsMonHom (fixedDimensionHilbertFullLevelDataFamilyIso S n P g Pm Pi N D).hom := by
  have := LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso_isMonHom S n P g Pm Pi N
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D)
  dsimp only [fixedDimensionHilbertFullLevelDataFamilyIso, Iso.trans_hom]
  infer_instance

theorem fixedDimensionHilbertFullLevelDataFamilyIso_level :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D).left).transport
        (fixedDimensionHilbertFullLevelDataFamilyIso S n P g Pm Pi N D) =
          (D.family S n P g Pm Pi N).level := by
  exact fullLevel_transport_comp_eq _ _ _ _ _
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso_level S n P g Pm Pi N
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D))
    (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso_level _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelDataRecovery
