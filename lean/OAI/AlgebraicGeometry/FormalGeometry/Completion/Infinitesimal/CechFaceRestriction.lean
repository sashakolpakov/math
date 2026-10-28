import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechCoordinates
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechFaces

/-! # Cech Face Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaceRestriction.Construction

noncomputable section

/-! The actual affine factor comparisons commute with the Cech face restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- Literal restriction between the two intersection factors of a Cech face. -/
def relativeCechFaceRestriction (q : ℕ) (k : Fin (q + 2)) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (q + 1)) :
    RelativeCechTerms.Construction.relativeCechFactor f U q (a.delete k) ⟶ RelativeCechTerms.Construction.relativeCechFactor f U (q + 1) a :=
  (RelativeStructureSections.Construction.relativeStructureSections f).map
    (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op

variable [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))

theorem infinitesimalCechFactorIso_mk (n q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (s : RelativeCechTerms.Construction.relativeCechFactor f U q a) :
    (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n q a).hom (Submodule.Quotient.mk s) =
      ((RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).mapIso
        (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)))
          U q a.val)).symm.op).hom
        ((RelativeStructureSections.Construction.relativeStructureSectionsPullback f (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n))).app
          (op (∏ᶜ fun k : Fin (q + 1) => U (a.val k))) s) := by
  change ((RelativeStructureSections.Construction.relativeStructureSections _).mapIso _).hom
    (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n _
      (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU q a.val) (Submodule.Quotient.mk s)) = _
  rw [ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv_mk]

/-- Canonical quotient pullback on each chart commutes with its Cech restriction. -/
theorem infinitesimalCechFactorIso_face (n q : ℕ) (k : Fin (q + 2))
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι (q + 1)) :
    (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n q (a.delete k)).hom ≫
        relativeCechFaceRestriction (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
          (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) q k a =
      (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map (relativeCechFaceRestriction f U q k a) ≫
        (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n (q + 1) a).hom := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  let P := RelativeStructureSections.Construction.relativeStructureSections (g ≫ f)
  let φ := RelativeStructureSections.Construction.relativeStructureSectionsPullback f g
  let V₀ := ∏ᶜ fun j : Fin (q + 1) => U ((a.delete k).val j)
  let V₁ := ∏ᶜ fun j : Fin (q + 1 + 1) => U (a.val j)
  let e₀ := (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection g) U q (a.delete k).val)).symm.op
  let e₁ := (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection g) U (q + 1) a.val)).symm.op
  let j := (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op
  have hn : (RelativeStructureSections.Construction.relativeStructureSections f).map j ≫ φ.app (op V₁) =
      φ.app (op V₀) ≫ P.map ((TopologicalSpace.Opens.map g.base).op.map j) :=
    φ.naturality j
  have hc : φ.app (op V₀) ≫ (P.mapIso e₀).hom ≫
      relativeCechFaceRestriction (g ≫ f) (fun i => g ⁻¹ᵁ U i) q k a =
        relativeCechFaceRestriction f U q k a ≫ φ.app (op V₁) ≫ (P.mapIso e₁).hom := by
    change φ.app (op V₀) ≫ (P.mapIso e₀).hom ≫ _ =
      (RelativeStructureSections.Construction.relativeStructureSections f).map j ≫ φ.app (op V₁) ≫ (P.mapIso e₁).hom
    rw [← Category.assoc ((RelativeStructureSections.Construction.relativeStructureSections f).map j) (φ.app (op V₁)) (P.mapIso e₁).hom,
      hn, Category.assoc]
    apply congrArg (fun m => φ.app (op V₀) ≫ m)
    dsimp only [relativeCechFaceRestriction, Functor.mapIso_hom, Functor.comp_map]
    rw [← P.map_comp, ← P.map_comp]
    congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ s =>
      change relativeCechFaceRestriction (g ≫ f) (fun i => g ⁻¹ᵁ U i) q k a
        ((CechTerms.Construction.infinitesimalCechFactorIso I f U hU n q (a.delete k)).hom (Submodule.Quotient.mk s)) =
          (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n (q + 1) a).hom
            (Submodule.Quotient.mk (relativeCechFaceRestriction f U q k a s))
      rw [infinitesimalCechFactorIso_mk, infinitesimalCechFactorIso_mk]
      exact ConcreteCategory.congr_hom hc s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaceRestriction.Construction
