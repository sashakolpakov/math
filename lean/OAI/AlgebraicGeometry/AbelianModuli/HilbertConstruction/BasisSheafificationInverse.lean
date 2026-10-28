import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationMaps

/-! # Basis Sheafification Inverse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationInverse.PresheafModuleBasisMap

noncomputable section

/-! A basis-wise linear isomorphism to a sheaf gives a compatible inverse into the source sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} {B : ι → X.Opens} {P : X.PresheafOfModules} {N : X.Modules}
variable (D : PresheafModuleBasisMaps.PresheafModuleBasisMap B P N) (hD : ∀ i, Function.Bijective (D.app i))

local instance (V : X.Opens) : Module Γ(X, V) (P.obj (.op V)) := (P.obj (.op V)).isModule

local instance (V : X.Opens) : Module Γ(X, V)
    Γ(((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P : X.Modules), V) :=
  (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.obj (.op V)).isModule

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps.PresheafModuleBasisMap.basisEquiv (i : ι) : P.obj (.op (B i)) ≃ₗ[Γ(X, B i)] Γ(N, B i) :=
  LinearEquiv.ofBijective (D.app i) (hD i)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps.PresheafModuleBasisMap.basisEquiv_symm_restrict (i j : ι) (h : B i ≤ B j) (x : Γ(N, B j)) :
    (D.basisEquiv hD i).symm (N.presheaf.map (homOfLE h).op x) =
      P.map (homOfLE h).op ((D.basisEquiv hD j).symm x) := by
  apply (D.basisEquiv hD i).injective
  exact ((D.basisEquiv hD i).apply_symm_apply _).trans
    ((congrArg (N.presheaf.map (homOfLE h).op) ((D.basisEquiv hD j).apply_symm_apply x)).symm.trans
      (D.naturality i j h ((D.basisEquiv hD j).symm x)).symm)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafModuleBasisMaps.PresheafModuleBasisMap.inverseBasisMap : HilbertConstruction.Module.MapBasisExtension.ModuleBasisMap B N ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) where
  app i :=
    (show P.obj (.op (B i)) →ₗ[Γ(X, B i)]
        Γ(((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P : X.Modules), B i) from
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (.op (B i))).hom).comp
      (D.basisEquiv hD i).symm.toLinearMap
  naturality i j h x := by
    have he := congrArg
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (.op (B i)))
      (D.basisEquiv_symm_restrict hD i j h x)
    exact he.trans (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
      (homOfLE h).op ((D.basisEquiv hD j).symm x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationInverse.PresheafModuleBasisMap
