import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ComplexConstants
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.GlobalSectionNaturality

/-! # Complex Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants

noncomputable section

/-! Affine-open coefficient constants are restrictions of the
actual global complex constants from the given structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def complexGlobalSectionMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : ℂ →+* Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom

theorem openComplexConstant_global (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (U : X.left.Opens) (hU : IsAffineOpen U) (c : ℂ) :
    let Y := Over.mk (U.ι ≫ X.hom)
    let : IsAffine Y.left := hU
    U.topIso.hom (algebraMap ℂ Γ(Y.left, ⊤) c) =
      X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (complexGlobalSectionMap X c) := by
  let Y := Over.mk (U.ι ≫ X.hom)
  let : IsAffine Y.left := hU
  let : LocallyOfFiniteType Y.hom := by change LocallyOfFiniteType (U.ι ≫ X.hom); infer_instance
  let : IsReduced Y.left := inferInstanceAs (IsReduced U.toScheme)
  have h := congrArg U.topIso.hom (Affine.ComplexConstants.affineComplexConstant_structure Y c)
  exact h.trans (GlobalSectionNaturality.openTopSection_global U (complexGlobalSectionMap X c))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants
