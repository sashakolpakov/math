import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection

/-! # Coefficient Linear -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.CoefficientLinear

noncomputable section

/-! Global section coefficients in actual affine frames are linear over
global functions. Frame generation supplies a coefficient outside every prime ideal. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

@[instance_reducible]
def openSectionsAlgebra (X : Scheme.{u}) (U : X.Opens) :
    Algebra Γ(X, ⊤) Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.toAlgebra

def frameCoefficientLinear {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    letI := openSectionsAlgebra X U
    Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, U) := by
  let := openSectionsAlgebra X U
  refine { toFun := SheafCohomology.Projective.FrameSections.overTrivializationCoefficient M U e, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    unfold SheafCohomology.Projective.FrameSections.overTrivializationCoefficient
    rw [map_add, map_add]
  · intro a b
    exact SheafCohomology.Projective.FrameSections.overTrivializationCoefficient_smul M U e a b

theorem frameCoefficientLinear_section {X : Scheme.{u}} {M : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    frameCoefficientLinear M U e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) =
      e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (1 : Γ(X, U))) := by
  have h := PresheafOfModules.naturality_apply s.val
    (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))
  change s.app U (X.presheaf.map (homOfLE le_top).op 1) =
    M.presheaf.map (homOfLE le_top).op (s.app ⊤ (1 : Γ(X, ⊤))) at h
  rw [map_one] at h
  exact congrArg (e.hom.val.app (.op (Over.mk (𝟙 U)))) h.symm

theorem frameCoefficientLinear_nonvanishing {X : Scheme.{u}} {M : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ U =
      X.basicOpen (frameCoefficientLinear M U e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)) := by
  apply Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.nonvanishing s U e
  apply Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.coordinate_eq
  exact (frameCoefficientLinear_section s U e).symm

theorem frameCoefficientLinear_avoids_prime {X : Scheme.{u}} {M : X.Modules}
    (hM : SectionDetection.Construction.HasFrameSections M) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (p : PrimeSpectrum Γ(X, U)) :
    ∃ s : Γ(M, ⊤), frameCoefficientLinear M U e s ∉ p.asIdeal := by
  have hxU : hU.fromSpec p ∈ U := by
    exact hU.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨s, hs⟩ := hM (hU.fromSpec p)
  refine ⟨AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s, ?_⟩
  have hx : hU.fromSpec p ∈
      X.basicOpen (frameCoefficientLinear M U e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)) :=
    (frameCoefficientLinear_nonvanishing s U e) ▸ ⟨hs, hxU⟩
  have hp : p ∈ hU.fromSpec ⁻¹ᵁ
      X.basicOpen (frameCoefficientLinear M U e (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)) := hx
  rw [hU.fromSpec_preimage_basicOpen] at hp
  exact hp

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.CoefficientLinear
