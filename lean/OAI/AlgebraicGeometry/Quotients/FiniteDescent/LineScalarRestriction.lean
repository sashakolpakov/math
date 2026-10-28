import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarsEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Line Scalar Restriction -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarRestriction.Construction.LineScalars

noncomputable section

/-! Endomorphism coordinates on overlapping line-bundle frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem frameValue_homOfLE {M : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (eU : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.toScheme) (a : End M) :
    (X.homOfLE h).appTop (LineScalarsEq.Construction.LineScalars.frameValue eU ((Scheme.Modules.pullback U.ι).map a)) =
      LineScalarsEq.Construction.LineScalars.frameValue eV ((Scheme.Modules.pullback V.ι).map a) := by
  let g := X.homOfLE h
  let δ : Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback V.ι :=
    Scheme.Modules.pullbackComp g U.ι ≪≫ Scheme.Modules.pullbackCongr (X.homOfLE_ι h)
  let ec := δ.app M ≪≫ eV
  exact (LineScalarsEq.Construction.LineScalars.frameValue_pullback g eU ec ((Scheme.Modules.pullback U.ι).map a)).symm.trans
    (LineScalarsEq.Construction.LineScalars.frameValue_functorComparison δ ec eV a)

theorem topIso_homOfLE {U V : X.Opens} (h : V ≤ U) (r : Γ(U.toScheme, ⊤)) :
    X.presheaf.map (homOfLE h).op (U.topIso.hom r) =
      V.topIso.hom ((X.homOfLE h).appTop r) := by
  exact (ConcreteCategory.congr_hom
    (X.restrictFunctorΓ.hom.naturality (homOfLE h).op) r).symm

theorem topIso_appTop (U : X.Opens) (r : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop r) = X.presheaf.map U.leTop.op r := by
  have h : U.ι.appTop ≫ U.topIso.hom = X.presheaf.map U.leTop.op := by
    change X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op ≫
      X.presheaf.map (eqToHom U.ι_image_top.symm).op = X.presheaf.map U.leTop.op
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom h r

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarRestriction.Construction.LineScalars
