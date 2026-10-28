import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtensionIterated
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechShort

/-! # Ordinary Affine Two -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryAffineTwo

noncomputable section

/-! Canonical affine base change on ordinary Cech section coordinates in
the three degrees needed for section lifting. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrdinaryAffineCechTerms

variable {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable {ι : Type u} [Finite ι] (U : ι → X.Opens)

def factor (W : X.Opens) (hW : IsAffineOpen W) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom
      (A := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op W))
      (B := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ W)))
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M W) :=
  AffineOpen.Construction.AffineOpenSquare.data f π ρ g h M ⟨W, hW⟩

def zeroData (hU : ∀ i, IsAffineOpen (U i)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom
      (A := (CechShort.Construction.CechShortCoordinates.target π M U).X₁)
      (B := (CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M)
        (fun i => f ⁻¹ᵁ U i)).X₁)
      (fun s i => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i) (s i)) :=
  PiExtension.Construction.FinitePiExtension.data g.appTop.hom
    (fun i => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op (U i)))
    (fun i => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U i)))
    (fun i => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i))
    (fun i => factor f π ρ g h M (U i) (hU i))

def oneData (hU : ∀ i j, IsAffineOpen (U i ⊓ U j)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom
      (A := (CechShort.Construction.CechShortCoordinates.target π M U).X₂)
      (B := (CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M)
        (fun i => f ⁻¹ᵁ U i)).X₂)
      (fun s i j => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i ⊓ U j) (s i j)) :=
  PiExtensionIterated.Construction.FinitePiExtension.data2 g.appTop.hom
    (fun i j => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op (U i ⊓ U j)))
    (fun i j => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj
      (op (f ⁻¹ᵁ (U i ⊓ U j))))
    (fun i j => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M (U i ⊓ U j))
    (fun i j => factor f π ρ g h M (U i ⊓ U j) (hU i j))

def twoData (hU : ∀ i j k, IsAffineOpen ((U i ⊓ U j) ⊓ U k)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data g.appTop.hom
      (A := (CechShort.Construction.CechShortCoordinates.target π M U).X₃)
      (B := (CechShort.Construction.CechShortCoordinates.target ρ ((Scheme.Modules.pullback f).obj M)
        (fun i => f ⁻¹ᵁ U i)).X₃)
      (fun s i j k => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ((U i ⊓ U j) ⊓ U k) (s i j k)) :=
  PiExtensionIterated.Construction.FinitePiExtension.data3 g.appTop.hom
    (fun i j k => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ((U i ⊓ U j) ⊓ U k)))
    (fun i j k => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj
      (op (f ⁻¹ᵁ ((U i ⊓ U j) ⊓ U k))))
    (fun i j k => PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ((U i ⊓ U j) ⊓ U k))
    (fun i j k => factor f π ρ g h M ((U i ⊓ U j) ⊓ U k) (hU i j k))

end Construction.OrdinaryAffineCechTerms

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrdinaryAffineTwo
