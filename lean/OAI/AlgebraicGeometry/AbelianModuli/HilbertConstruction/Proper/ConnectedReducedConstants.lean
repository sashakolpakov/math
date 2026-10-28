import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IntegralAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FactorThroughConstants
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Connected Reduced Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants

noncomputable section

/-! Global functions on a connected reduced universally closed scheme over a field form a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

theorem properConnectedReduced_globalSections_isField (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X] : IsField Γ(X, ⊤) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    X.toSpecΓ.denseRange.preconnectedSpace X.toSpecΓ.continuous
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have hp : p.appTop.hom.IsIntegral := isIntegral_appTop_of_universallyClosed p
  algebraize [p.appTop.hom]
  exact Connected.IntegralAlgebra.connected_integral_reduced_isField Γ(Spec (.of K), ⊤) Γ(X, ⊤)

def properConnectedReducedPointGlobalIso (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) : Γ(Spec (.of K), ⊤) ≅ Γ(X, ⊤) := by
  letI : Field Γ(X, ⊤) := (properConnectedReduced_globalSections_isField p).toField
  have : Mono x.appTop := ConcreteCategory.mono_of_injective x.appTop x.appTop.hom.injective
  have hpx : p.appTop ≫ x.appTop = 𝟙 _ :=
    (Scheme.Hom.comp_appTop x p).symm.trans
      ((congrArg Scheme.Hom.appTop hx).trans Scheme.Hom.id_appTop)
  refine ⟨p.appTop, x.appTop, hpx, ?_⟩
  apply (cancel_mono x.appTop).mp
  rw [Category.assoc, hpx, Category.comp_id, Category.id_comp]

theorem properConnectedReduced_map_eq_constant (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X] (f : X ⟶ Y) [IsAffine Y]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) : f = p ≫ x ≫ f := by
  let : IsIso p.appTop := (properConnectedReducedPointGlobalIso p x hx).isIso_hom
  obtain ⟨a, ha, _⟩ := Affine.FactorThroughConstants.affineFactorOfGlobalIso_existsUnique p f
  have hxa : x ≫ f = a := by rw [← ha, ← Category.assoc, hx, Category.id_comp]
  exact ha.symm.trans (congrArg (fun b => p ≫ b) hxa.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
