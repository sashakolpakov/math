import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Slice
import Mathlib.RingTheory.Etale.Descent

/-! # Coefficient Algebra Properties -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientAlgebraProperties.Construction

noncomputable section

/-!
# Completion: the actual finite coefficient coordinate algebra is finite étale

The properties come from the checked isomorphism to the disjoint union of
the base, followed by the spectrum criteria for finite and étale morphisms.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) [NeZero (ℓ ^ n)] (S : Type u) [CommRing S]

theorem finiteCoefficientAlgebra_spec_finite :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj))) := by
  let e := ProEtale.Slice.Construction.finiteCoefficientAlgebraSpecIso ℓ n S
  have : IsFinite (ConstantScheme.Construction.finiteCoefficientProEt ℓ n (Spec (CommRingCat.of S))).hom :=
    ConstantScheme.Construction.finiteCoefficientProEt_finite ℓ n _
  have : IsIso e.hom.left :=
    (Scheme.ProEt.forget _ ⋙ Over.forget _).map_isIso e.hom
  change IsFinite ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec S).obj (op (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S))).hom
  rw [← MorphismProperty.Over.w e.hom]
  infer_instance

theorem finiteCoefficientAlgebra_spec_etale :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj))) := by
  let e := ProEtale.Slice.Construction.finiteCoefficientAlgebraSpecIso ℓ n S
  have : Etale (ConstantScheme.Construction.finiteCoefficientProEt ℓ n (Spec (CommRingCat.of S))).hom :=
    ConstantScheme.Construction.finiteConstantScheme_etale _ _
  have : IsIso e.hom.left :=
    (Scheme.ProEt.forget _ ⋙ Over.forget _).map_isIso e.hom
  change Etale ((ProEtale.Algebras.Construction.proEtaleAlgebraSpec S).obj (op (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S))).hom
  rw [← MorphismProperty.Over.w e.hom]
  infer_instance

/-- Finiteness of the actual local coordinate algebra as a module. -/
theorem finiteCoefficientAlgebra_finite : Module.Finite S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj := by
  have h := (IsFinite.SpecMap_iff _).mp (finiteCoefficientAlgebra_spec_finite ℓ n S)
  exact (RingHom.finite_algebraMap).mp h

/-- Étaleness of the actual local coordinate algebra over its base ring. -/
theorem finiteCoefficientAlgebra_etale : Algebra.Etale S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj := by
  have h := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (finiteCoefficientAlgebra_spec_etale ℓ n S)
  exact (RingHom.etale_algebraMap).mp h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientAlgebraProperties.Construction
