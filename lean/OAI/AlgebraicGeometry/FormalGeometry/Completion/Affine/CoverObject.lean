import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Slice
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.AlgebraBaseChange

/-! # Cover Object -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverObject.Construction

noncomputable section

/-!
# Completion: values of the actual site sheaf on weakly étale algebras

The comparison with a covering scheme uses identity maps on spectra,
with the structure morphisms compared by the composition law for Spec.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))

/-- The actual covering scheme determined by the weakly étale ring map. -/
def affineCoverObject : (Spec (CommRingCat.of R)).ProEt :=
  have := hf
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom f))

/-- Affine objects over the covering ring, viewed in the original slice site. -/
def affineAlgebraToSlice : (ProEtale.Algebras.Construction.ProEtaleAlgebra S)ᵒᵖ ⥤ Over (affineCoverObject f hf) :=
  ProEtale.Algebras.Construction.proEtaleAlgebraSpec S ⋙ ProEtale.Slice.Construction.proEtaleToSlice (affineCoverObject f hf)

def affineAlgebraToSliceFullyFaithful : (affineAlgebraToSlice f hf).FullyFaithful :=
  ProEtale.Algebras.Construction.proEtaleAlgebraSpecFullyFaithful.comp (ProEtale.Slice.Construction.proEtaleToSliceFullyFaithful _)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.CoverObject.Construction
