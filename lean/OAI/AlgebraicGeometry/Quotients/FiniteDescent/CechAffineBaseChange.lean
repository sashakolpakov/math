import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechTensorProducts
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalizedScalar

/-! # Cech Affine Base Change -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange

noncomputable section

/-! Canonical base change of ordered affine Cech complexes across affine base schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def factorData (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (hU : IsAffineOpen (∏ᶜ fun k => U (i.1 k))) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom
      (A := SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1)
      (B := SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1)
      (fun s => ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm).op
          (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (∏ᶜ fun k => U (i.1 k)) s)) := by
  let A := SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1
  let B := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj
    (op (f ⁻¹ᵁ (∏ᶜ fun k => U (i.1 k))))
  let C := SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1
  let v : A → B := PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (∏ᶜ fun k => U (i.1 k))
  let e : NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom v :=
    @AffineOpen.Construction.AffineOpenSquare.data X Y S T ‹IsAffine S› ‹IsAffine T› f π ρ g h M
      ‹M.IsQuasicoherent› ⟨_, hU⟩
  let d : B ≅ C := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).mapIso
    (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm).op
  exact @NormalizedScalar.Construction.NormalizedScalarIso.post Γ(S, ⊤) Γ(T, ⊤) inferInstance inferInstance g.appTop.hom
    A B C v e d

def factorIso (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (hU : IsAffineOpen (∏ᶜ fun k => U (i.1 k))) :
    (ModuleCat.extendScalars g.appTop.hom).obj (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1) ≅
      SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1 :=
  (factorData f π ρ g h M U q i hU).val

theorem factorIso_one (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (hU : IsAffineOpen (∏ᶜ fun k => U (i.1 k))) (s : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1) :
    (factorIso f π ρ g h M U q i hU).hom ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U q i.1).symm).op
          (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (∏ᶜ fun k => U (i.1 k)) s) :=
  (factorData f π ρ g h M U q i hU).property s

theorem tensorFactor_isIso (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q)
    (hU : IsAffineOpen (∏ᶜ fun k => U (i.1 k))) :
    IsIso (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h.w M U q i) := by
  exact @NormalizedScalar.Construction.NormalizedScalarIso.isIso Γ(S, ⊤) Γ(T, ⊤) inferInstance inferInstance g.appTop.hom
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U q i.1)
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor ρ ((Scheme.Modules.pullback f).obj M) (fun j => f ⁻¹ᵁ U j) q i.1)
    _ (factorData f π ρ g h M U q i hU) (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h.w M U q i)
    (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor_one f π ρ g h.w M U q i)

theorem isIso_of_affine_intersections [Finite ι]
    (hU : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k))) :
    IsIso (CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h.w M U) := by
  have (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : IsIso (CechBaseChangeFactors.Construction.CechBaseChangeMap.tensorFactor f π ρ g h.w M U q i) :=
    tensorFactor_isIso f π ρ g h M U q i (hU q i)
  exact CechTensorProducts.Construction.CechBaseChangeMap.isIso_of_factors f π ρ g h.w M U

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange
