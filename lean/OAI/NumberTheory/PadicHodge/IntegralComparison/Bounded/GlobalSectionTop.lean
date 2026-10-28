import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.GlobalSectionTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone

/-! # Global Section Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GlobalSectionTop

noncomputable section

/-! The canonical bounded crystalline global restriction factors
through the genuine global-to-top-open section isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) fY n
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n

variable (K : CochainComplex
  (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) ℕ)

def complexIso : ((G).mapHomologicalComplex (.up ℕ)).obj K ≅
    (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.global Y.Opens).obj (((O).mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ModuleCat.uliftFunctor.{u+2,u+1} R).mapIso
      (BoundedOpen.SectionGlobal.linearEquiv fY n (K.X i)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

theorem component (i : ℕ) (V : Y.Opens) : (complexIso fY n K).hom.f i ≫
    ((O).obj (K.X i)).map (homOfLE (le_top : V ≤ ⊤)).op =
      ((GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).app (K.X i)).app (op V) :=
  Incoming.GlobalSectionTop.lifted.{u+1,u,u+1,u,u+2} R (ModuleCat.of R R)
    (BoundedOpen.SectionPresheaf.property fY n)
    (BoundedOpen.SectionPresheaf.monotone fY n)
    (BoundedOpen.Support.property_top fY n) (K.X i).obj V

theorem cone : ((Functor.const Y.Opensᵒᵖ).mapHomologicalComplex (.up ℕ)).map
      (complexIso fY n K).hom ≫
    GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone Y.Opens (((O).mapHomologicalComplex (.up ℕ)).obj K) =
      ((GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).mapHomologicalComplex (.up ℕ)).app K := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  exact component fY n K i V.unop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GlobalSectionTop
