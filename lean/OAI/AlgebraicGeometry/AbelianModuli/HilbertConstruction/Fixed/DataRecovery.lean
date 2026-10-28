import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.UniversalRecovery

/-! # Data Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Equality of abelian data preserves the group structure. Applying this
to the representing equivalence gives universal-family recovery for each
native abelian datum, without a separate compatibility hypothesis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

section Equality
variable {S : Scheme.{u}} {g : ℕ}

def Abelian.Schemes.AbelianScheme.eqSchemeIso {A B : Abelian.Schemes.AbelianScheme g S} (h : A = B) : A.scheme ≅ B.scheme :=
  eqToIso (congrArg Abelian.Schemes.AbelianScheme.scheme h)

instance Abelian.Schemes.AbelianScheme.eqSchemeIso_isMonHom {A B : Abelian.Schemes.AbelianScheme g S} (h : A = B) :
    IsMonHom (Abelian.Schemes.AbelianScheme.eqSchemeIso h).hom := by
  subst B
  exact inferInstanceAs (IsMonHom (𝟙 A.scheme))

end Equality

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)
variable {T : Over S} (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T)

def Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso :
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D).left).scheme ≅
        (D.abelianScheme S n P g Pm Pi).scheme :=
  Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi
    ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D) ≪≫
      Abelian.Schemes.AbelianScheme.eqSchemeIso
        (congrArg (fun E : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T =>
          E.abelianScheme S n P g Pm Pi)
          ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).apply_symm_apply D))

instance Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso_isMonHom :
    IsMonHom (Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n P g Pm Pi D).hom := by
  dsimp only [Fixed.DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso, Iso.trans_hom]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
