import OAI.RepresentationTheory.Theta.Geometric.StandardSmoothLocalization
import Mathlib.AlgebraicGeometry.AffineScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints

/-! # Spec Localization Properties -/

namespace OAI.RepresentationTheory.Theta.Geometric.SpecLocalizationProperties

noncomputable section

/-! The standard smooth localization properties hold for the literal
global functions on its spectrum, with the canonical geometric scalar map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

universe u

@[instance_reducible]
def specGlobalAlgebra (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Algebra R Γ(Spec (.of S), ⊤) :=
  ((Scheme.ΓSpecIso (.of S)).inv.hom.comp (algebraMap R S)).toAlgebra

def specGlobalAlgebraEquiv (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    letI := specGlobalAlgebra R S
    S ≃ₐ[R] Γ(Spec (.of S), ⊤) := by
  letI := specGlobalAlgebra R S
  exact { __ := (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv.symm, commutes' := fun _ => rfl }

theorem specGlobalAlgebra_geometric (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S))).symm r

theorem specGlobalAlgebra_pointMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv (Spec (.of S)) (.of R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      (Scheme.ΓSpecIso (.of S)).inv.hom.comp (algebraMap R S) := by
  ext r
  exact specGlobalAlgebra_geometric R S r

theorem standardSmooth_spec_localization_properties
    {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    [Nontrivial S] (W : Submonoid P) [IsLocalization W S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R P] :
    letI := specGlobalAlgebra R S
    Algebra.FormallySmooth R Γ(Spec (.of S), ⊤) ∧ Module.Flat R Γ(Spec (.of S), ⊤) ∧
      Module.Free Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R] ∧
      Module.Finite Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R] ∧
      Module.finrank Γ(Spec (.of S), ⊤) Ω[Γ(Spec (.of S), ⊤)⁄R] = n := by
  let := specGlobalAlgebra R S
  let := specGlobalAlgebra P S
  have : Nontrivial Γ(Spec (.of S), ⊤) :=
    RingHom.domain_nontrivial (Scheme.ΓSpecIso (.of S)).hom.hom
  have : IsScalarTower R P Γ(Spec (.of S), ⊤) := IsScalarTower.of_algebraMap_eq (by
    intro r
    change (Scheme.ΓSpecIso (.of S)).inv (algebraMap R S r) =
      (Scheme.ΓSpecIso (.of S)).inv (algebraMap P S (algebraMap R P r))
    rw [IsScalarTower.algebraMap_apply R P S])
  have : IsLocalization W Γ(Spec (.of S), ⊤) :=
    IsLocalization.isLocalization_of_algEquiv W (specGlobalAlgebraEquiv P S)
  exact StandardSmoothLocalization.standardSmooth_localization_properties W n

end

end OAI.RepresentationTheory.Theta.Geometric.SpecLocalizationProperties
