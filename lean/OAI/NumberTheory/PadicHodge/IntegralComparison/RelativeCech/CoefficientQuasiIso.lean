import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.AffineHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains

/-! # Coefficient Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso

noncomputable section

/-! Relative augmented Čech totals preserve quasicoherent quasi-isomorphisms
on affine intersections, without requiring the family to cover the ambient scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens)
  (hV : ∀ i, IsAffineOpen (V i))

include hU hV in
theorem intersection_affine (p : ℕ) (a : AugmentedOrdered.Cech.Index ι p) :
    IsAffineOpen (U ⊓ (AugmentedOrdered.Cech.formal V p).obj a) := by
  cases p with
  | zero =>
    have he : (AugmentedOrdered.Cech.formal V 0).obj a = ⊤ := by
      change (∏ᶜ fun j : Fin 0 => V (a.val j)) = ⊤
      apply le_antisymm le_top
      exact leOfHom (Pi.lift (fun j => Fin.elim0 j))
    simpa only [he, inf_top_eq] using hU
  | succ p =>
    exact hU.inf (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection V hV p a.val)

abbrev coefficients (K : CochainComplex X.Modules ℕ) :=
  ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ)).obj K

abbrev coefficientMap {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :=
  ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ)).map a

include hU hV in
theorem quasiIso {K L : CochainComplex X.Modules ℕ}
    [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
    (a : K ⟶ L) [QuasiIso a] :
    QuasiIso (Total.sourceMap U V (coefficientMap π a)) := by
  apply AugmentedOrdered.CechQuasiIso.quasiIso_of_evaluation V Γ(S, ⊤)
    (((Refinement.restriction U).mapHomologicalComplex (.up ℕ)).map
      (coefficientMap π a))
  intro p i
  exact Geometric.AffineHomology.quasiIso π _ (intersection_affine U hU V hV p i) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso
