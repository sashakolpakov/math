import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PurityConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalDualLine

/-! # Complement Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementAdjunction

noncomputable section

/-! On an affine open outside a closed subscheme, both the original
dual cohomology and every direct-image module vanish. Their unique
identification is the complement piece of local adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section DirectImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : X.Modules) (U : Y.Opens)
  (hunit : RingHom.ker (f.app U).hom = ⊤)

include hunit in
theorem directImage_sections_zero :
    IsZero ((Affine.ModuleExactSections.sections U).obj
      ((Scheme.Modules.pushforward f).obj N)) := by
  have h1 : (f.app U).hom 1 = 0 := by
    change (1 : Γ(Y, U)) ∈ RingHom.ker (f.app U).hom
    rw [hunit]
    trivial
  have h01 : (0 : Γ(X, f ⁻¹ᵁ U)) = 1 := h1.symm.trans (map_one _)
  let : Subsingleton Γ(X, f ⁻¹ᵁ U) := subsingleton_of_zero_eq_one h01
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton Γ(N, f ⁻¹ᵁ U)
  exact Module.subsingleton Γ(X, f ⁻¹ᵁ U) _

end DirectImage

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (j : σ) (B b : ℕ) (hb : b ≤ B)
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (i : σ) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (hunit : RingHom.ker (f.app U).hom = ⊤) (c : ℕ)

include hb hU i hUi hunit in
omit [LinearOrder σ] in
theorem dual_sections_zero :
    IsZero ((Affine.ModuleExactSections.sections U).obj
      ((ClosedImmersionPurity.internalComplex f j B b).homology c)) := by
  let (q : ℕ) : ((ClosedImmersionPurity.internalComplex f j B b).X q).IsQuasicoherent :=
    LocalDualLine.term_quasicoherent f j B b hb q
  have h := PurityConcentration.exactAt_of_unit f j B b U hU i hUi hunit c
  have hz := (Affine.LocalExactness.homologyIso (ClosedImmersionPurity.internalComplex f j B b) U hU c).isZero_iff.mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h)
  let := AddCommGrpCat.subsingleton_of_isZero hz
  exact ModuleCat.isZero_of_subsingleton _

def sectionIso (N : X.Modules) :
    (Affine.ModuleExactSections.sections U).obj ((ClosedImmersionPurity.internalComplex f j B b).homology c) ≅
      (Affine.ModuleExactSections.sections U).obj ((Scheme.Modules.pushforward f).obj N) :=
  (dual_sections_zero f j B b hb U hU i hUi hunit c).isoZero ≪≫
    (directImage_sections_zero f N U hunit).isoZero.symm

omit [LinearOrder σ] in
theorem sectionIso_hom (N : X.Modules) :
    (sectionIso f j B b hb U hU i hUi hunit c N).hom = 0 :=
  (dual_sections_zero f j B b hb U hU i hUi hunit c).eq_of_src _ _

def openIso (N : X.Modules) [N.IsQuasicoherent] :
    ((ClosedImmersionPurity.internalComplex f j B b).homology c).restrict U.ι ≅
      ((Scheme.Modules.pushforward f).obj N).restrict U.ι := by
  let := LocalDualLine.homology_quasicoherent f j B b hb c
  let := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f N
  exact AffineSection.Isomorphism.openIso U hU _ _
    (sectionIso f j B b hb U hU i hUi hunit c N)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementAdjunction
