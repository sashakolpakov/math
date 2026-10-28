import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionsSchemeIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Line Bundle Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections

noncomputable section

/-! Intrinsic spaces of sections of tensor powers are unchanged by isomorphisms of schemes and line bundles over the coefficient field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

def schemeGlobalSectionsBaseCongr {p q : X ⟶ Spec (.of R)} (h : p = q) (M : X.Modules) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M ≃ₗ[R] (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor q).obj M :=
  (eqToIso (congrArg (fun c => (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor c).obj M) h)).toLinearEquiv

def lineBundlePowerSectionsIso (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of R))
    (L : Line.Bundles.LineBundle Y) (M : Line.Bundles.LineBundle X) (e : (L.pullback f).sheaf ≅ M.sheaf) (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (L.tensorPower d).sheaf ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ p)).obj (M.tensorPower d).sheaf :=
  Global.SectionsSchemeIso.schemeGlobalSectionsCongr f p (L.powerBaseChangeIso f d ≪≫ (TensorPower.Maps.tensorPowerFunctor X d).mapIso e)

def lineBundlePowerSectionsOverIso {A B : Over (Spec (.of R))} (f : A ≅ B)
    (L : Line.Bundles.LineBundle B.left) (M : Line.Bundles.LineBundle A.left) (e : (L.pullback f.hom.left).sheaf ≅ M.sheaf) (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor B.hom).obj (L.tensorPower d).sheaf ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.hom).obj (M.tensorPower d).sheaf := by
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  exact (lineBundlePowerSectionsIso f.hom.left B.hom L M e d).trans
    (schemeGlobalSectionsBaseCongr f.hom.w (M.tensorPower d).sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections
